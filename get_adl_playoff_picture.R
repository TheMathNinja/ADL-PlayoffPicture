## This function gets ADL Playoff picture and Projected Draft Order 
## given season and (completed) week inputs

library(gt)
library(glue)
library(ffscrapr)
library(tidyverse)

# Load all MFL connection objects once into `mfl_conns`
source("C:/Users/filim/Documents/R/FFAucAndDraft/HelperFunctions/load_mfl_conns.R")
mfl_conns <- load_mfl_conns()

# Global constant: ADL regular season ends after 12 weeks
adl_max_week <- 12L

###############################################
## HELPER: Fast all-play from weekly scores  ##
###############################################
allplay_from_scores <- function(scores) {
  # scores: numeric vector of length n (points for all teams in a week)
  n <- length(scores)
  if (n <= 1L) return(rep(0, n))
  
  # Sort ascending
  o <- order(scores)
  s <- scores[o]
  
  # Run-length encode to find ties
  r <- rle(s)
  m <- r$lengths          # lengths of equal-score runs
  k <- length(m)
  
  # starting index of each run in the sorted vector
  starts    <- cumsum(c(1L, head(m, -1L)))
  # number of elements strictly less than the run
  less_than <- cumsum(c(0L, head(m, -1L)))
  
  ap_sorted <- numeric(n)
  for (j in seq_len(k)) {
    idx <- starts[j]:(starts[j] + m[j] - 1L)
    L   <- less_than[j]
    T   <- m[j]
    # AP wins formula: lower scores + 0.5 * (ties - 1)
    ap_sorted[idx] <- L + 0.5 * (T - 1L)
  }
  
  # unsort back to original order
  ap <- numeric(n)
  ap[o] <- ap_sorted
  ap
}

########################################################
## HELPER: Bonus wins from segment AP + points        ##
########################################################
bonus_from_segment <- function(ap_seg, pts_seg) {
  # ap_seg : numeric vector of segment AP wins
  # pts_seg: numeric vector of segment total points (tie-breaker)
  n <- length(ap_seg)
  if (length(pts_seg) != n) {
    stop("ap_seg and pts_seg must have the same length")
  }
  
  # Rank primarily by segment AP, secondarily by segment points
  ord <- order(ap_seg, pts_seg, decreasing = TRUE)
  ranks <- integer(n)
  ranks[ord] <- seq_len(n)
  
  res <- numeric(n)
  # Top 15: bonus win (1)
  res[ranks <= 15L] <- 1
  # 16–17: bonus tie (0.5)
  res[ranks > 15L & ranks <= 17L] <- 0.5
  # 18–32: bonus loss (0)
  res
}



# ============================================================
# FUNCTION: get_adl_paths()
#
# Purpose in workflow:
#   Centralizes all file paths used in the ADL playoff / modeling
#   pipeline (history caches, rating history, model comparison
#   outputs, etc.) so you have one place to change directories
#   and one object to pass around.
# ============================================================

get_adl_paths <- function(
    base_dir = "C:/Users/filim/Documents/R/LeagueFeatures/PlayoffPicture"
) {
  if (!dir.exists(base_dir)) dir.create(base_dir, recursive = TRUE)
  
  list(
    base_dir              = base_dir,
    history_completed     = file.path(base_dir, "ADL_weekly_history_completed.rds"),
    rating_hist_completed = file.path(base_dir, "rating_hist_completed.rds"),
    ap_model_comparison   = file.path(base_dir, "ap_model_comparison.rds"),
    h2h_model_comparison  = file.path(base_dir, "h2h_model_comparison.rds"),
    # current-season history cache, one file per season:
    history_current = function(season) {
      file.path(base_dir, paste0("ADL_weekly_history_", season, ".rds"))
    }
  )
}


# ============================================================
# FUNCTION: build_adl_weekly_primitives()
#
# Purpose in workflow:
#   For a given season, builds the *weekly primitives* that all
#   downstream modeling uses:
#     - weekly points for
#     - weekly potential points
#     - weekly H2H W/L/T counts
#     - weekly all-play wins (APW)
#     - NEW: weekly offense / defense / special teams / bench splits:
#         * offense_points_week        (QB, RB, WR, TE)
#         * defense_points_week        (DT, DE, LB, CB, S)
#         * specialteams_points_week   (PK, PN)
#         * bench_points_week          (starter_status == "nonstarter")
#         * offst_points_week = offense + special teams
#
#   Output: one row per (season, week, team) with only the
#   minimal fields needed to later derive:
#     - cumulative standings
#     - APW prediction models
#     - Monte Carlo simulations, etc.
# ============================================================

build_adl_weekly_primitives <- function(season, max_week = adl_max_week) {
  
  # Derive connection name for this season (e.g., "ADL25")
  season_suffix <- substr(as.character(season), 3, 4)  # 2025 -> "25"
  conn_name     <- paste0("ADL", season_suffix)        # "ADL25"
  
  mfl_conn <- mfl_conns[[conn_name]]
  if (is.null(mfl_conn)) {
    stop("No MFL connection named ", conn_name, " found in load_mfl_conns().")
  }
  
  max_week <- min(max_week, adl_max_week)
  
  # 1. Franchises (metadata only) --------------------------------------
  franchises <- ffscrapr::ff_franchises(mfl_conn) %>%
    dplyr::select(
      franchise_id,
      dplyr::any_of(c("franchise_name", "name", "division", "conference"))
    )
  
  # 2. Schedule (weekly H2H + points_for_week) -------------------------
  sched <- ffscrapr::ff_schedule(mfl_conn) %>%
    dplyr::filter(week <= max_week) %>%
    dplyr::select(
      week, franchise_id, opponent_id,
      franchise_score, opponent_score, result
    )
  
  h2h_weekly <- sched %>%
    dplyr::group_by(franchise_id, week) %>%
    dplyr::summarise(
      h2h_wins_week_raw   = sum(franchise_score > opponent_score, na.rm = TRUE),
      h2h_ties_week_raw   = sum(franchise_score == opponent_score, na.rm = TRUE),
      h2h_losses_week_raw = sum(franchise_score < opponent_score, na.rm = TRUE),
      points_for_week     = sum(franchise_score, na.rm = TRUE),
      .groups = "drop"
    )
  
  # 3. Starters -> potential_points_week + O/D/ST/bench splits ---------
  starters <- ffscrapr::ff_starters(mfl_conn) %>%
    dplyr::filter(week <= max_week)
  
  weekly_pts_cats <- starters %>%
    dplyr::group_by(franchise_id, week) %>%
    dplyr::summarise(
      actual_from_starters  = sum(
        player_score[starter_status == "starter"],
        na.rm = TRUE
      ),
      potential_points_week = sum(
        player_score[should_start == 1],
        na.rm = TRUE
      ),
      
      offense_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("QB", "RB", "WR", "TE")
        ],
        na.rm = TRUE
      ),
      
      defense_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("DT", "DE", "LB", "CB", "S")
        ],
        na.rm = TRUE
      ),
      
      specialteams_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("PK", "PN")
        ],
        na.rm = TRUE
      ),
      
      bench_points_week = sum(
        player_score[starter_status == "nonstarter"],
        na.rm = TRUE
      ),
      
      offst_points_week = offense_points_week + specialteams_points_week,
      
      .groups = "drop"
    )
  
  weekly_scores <- h2h_weekly %>%
    dplyr::left_join(weekly_pts_cats, by = c("franchise_id", "week"))
  
  # Optional sanity check: starter totals vs schedule totals -----------
  mismatch <- weekly_scores %>%
    dplyr::filter(
      !is.na(actual_from_starters),
      abs(points_for_week - actual_from_starters) > 0.01
    ) %>%
    dplyr::left_join(franchises, by = "franchise_id")
  
  if (nrow(mismatch) > 0) {
    team_labels <- if ("franchise_name" %in% names(mismatch)) {
      paste0(
        "week ", mismatch$week,
        " – franchise_id ", mismatch$franchise_id,
        " (", mismatch$franchise_name, ")"
      )
    } else {
      paste0("week ", mismatch$week, " – franchise_id ", mismatch$franchise_id)
    }
    
    warning(
      "Starter-based points differ from ff_schedule points for ",
      nrow(mismatch), " team-week rows: ",
      paste(team_labels, collapse = "; ")
    )
  }
  
  # 4. Weekly all-play wins (fast, rank-based) -------------------------
  n_teams <- weekly_scores %>%
    dplyr::summarise(n_teams = dplyr::n_distinct(franchise_id)) %>%
    dplyr::pull(n_teams)
  
  if (n_teams != 32L) {
    warning("Expected 32 teams, found ", n_teams,
            ". All-play logic assumes 32-team ADL.")
  }
  
  allplay_weekly <- weekly_scores %>%
    dplyr::group_by(week) %>%
    dplyr::group_modify(~ {
      tibble::tibble(
        franchise_id = .x$franchise_id,
        ap_wins_week = allplay_from_scores(.x$points_for_week)
      )
    }) %>%
    dplyr::ungroup()
  
  weekly_scores %>%
    dplyr::left_join(allplay_weekly, by = c("franchise_id", "week")) %>%
    dplyr::left_join(franchises,      by = "franchise_id") %>%
    dplyr::mutate(season = !!season, .before = 1L) %>%
    dplyr::select(
      season,
      week,
      franchise_id,
      franchise_name,
      division,
      conference,
      
      # Weekly primitives
      points_for_week,
      potential_points_week,
      offense_points_week,
      defense_points_week,
      specialteams_points_week,
      bench_points_week,
      offst_points_week,
      h2h_wins_week_raw,
      h2h_ties_week_raw,
      h2h_losses_week_raw,
      ap_wins_week,
      
      # Raw starter-based check column if you ever want it
      actual_from_starters
    )
}



# ============================================================
# FUNCTION: build_adl_weekly_history()
#
# Purpose in workflow:
#   Uses build_adl_weekly_primitives() across one or more seasons
#   and adds all *cumulative* fields needed for:
#     - APW regression models
#     - H2H logistic models
#     - Monte Carlo modeling of bonus games, etc.
#
#   Output: one row per (season, week, team) with:
#     - weekly primitives (points_for_week, ap_wins_week, etc.)
#     - cumulative totals (points_for, ap_wins_total, h2h_wins, etc.)
#     - derived rates (win_pct, ap_win_pct)
# ============================================================

build_adl_weekly_history <- function(seasons, max_week = adl_max_week) {
  seasons  <- as.integer(seasons)
  max_week <- min(max_week, adl_max_week)
  
  weekly_raw <- purrr::map_dfr(seasons, function(season) {
    message("Building weekly primitives for ADL season ", season, " ...")
    build_adl_weekly_primitives(season = season, max_week = max_week)
  })
  
  # Optional diagnostic (not used, but handy if you want to inspect)
  teams_per_season <- weekly_raw %>%
    dplyr::group_by(season) %>%
    dplyr::summarise(
      n_teams = dplyr::n_distinct(franchise_id),
      .groups = "drop"
    )
  
  # Cumulative fields per season/team -------------------------------
  history_with_cums <- weekly_raw %>%
    dplyr::arrange(season, franchise_id, week) %>%
    dplyr::group_by(season, franchise_id) %>%
    dplyr::mutate(
      points_for       = cumsum(points_for_week),
      potential_points = cumsum(potential_points_week),
      ap_wins_total    = cumsum(ap_wins_week),
      
      h2h_wins_raw_total   = cumsum(h2h_wins_week_raw),
      h2h_ties_raw_total   = cumsum(h2h_ties_week_raw),
      h2h_losses_raw_total = cumsum(h2h_losses_week_raw),
      
      h2h_wins  = h2h_wins_raw_total + 0.5 * h2h_ties_raw_total,
      h2h_games = h2h_wins_raw_total + h2h_ties_raw_total + h2h_losses_raw_total,
      win_pct   = dplyr::if_else(h2h_games > 0, h2h_wins / h2h_games, 0)
    ) %>%
    dplyr::ungroup()
  
  # All-play games per team by season-week: (n_teams - 1) * week -----
  history_with_cums %>%
    dplyr::group_by(season, week) %>%
    dplyr::mutate(
      n_teams_season = dplyr::n_distinct(franchise_id),
      ap_games       = (n_teams_season - 1L) * week,
      ap_win_pct     = dplyr::if_else(ap_games > 0, ap_wins_total / ap_games, 0)
    ) %>%
    dplyr::ungroup() %>%
    dplyr::select(
      season,
      week,
      franchise_id,
      franchise_name,
      division,
      conference,
      
      # Weekly primitives
      points_for_week,
      potential_points_week,
      offense_points_week,
      defense_points_week,
      specialteams_points_week,
      bench_points_week,
      offst_points_week,
      h2h_wins_week_raw,
      h2h_ties_week_raw,
      h2h_losses_week_raw,
      ap_wins_week,
      
      # Cumulative standings-like fields
      points_for,
      potential_points,
      ap_wins_total,
      h2h_wins_raw_total,
      h2h_ties_raw_total,
      h2h_losses_raw_total,
      h2h_wins,
      h2h_games,
      win_pct,
      ap_games,
      ap_win_pct
    )
}



# ============================================================
# FUNCTION: build_adl_weekly_results()
#
# Purpose in workflow:
#   For a *single* season and snapshot week, builds the full
#   ADL standings table needed for:
#     - Playoff picture
#     - Bonus game tallies (W3 / W6 / W9 / W12 / Season)
#     - Total wins and win% (H2H + Bonus)
#
#   This is the "live standings" function used by your
#   playoff-picture wrapper, whereas build_adl_weekly_history()
#   is the historical modeling dataset builder.
# ============================================================

build_adl_weekly_results <- function(season, week) {
  
  # Derive connection name for this season (e.g., "ADL25")
  season_suffix <- substr(as.character(season), 3, 4)
  conn_name     <- paste0("ADL", season_suffix)
  
  mfl_conn <- mfl_conns[[conn_name]]
  if (is.null(mfl_conn)) {
    stop("No MFL connection named ", conn_name, " found in load_mfl_conns().")
  }
  
  # Snapshot cannot go beyond the ADL regular season
  week_max <- min(as.integer(week), adl_max_week)
  
  # 1. Franchises: id -> name, division, conference --------------------
  franchises <- ffscrapr::ff_franchises(mfl_conn) %>%
    dplyr::select(
      franchise_id,
      dplyr::any_of(c("franchise_name", "name", "division", "conference"))
    )
  
  # 2. Schedule (through given week, reg season only) ------------------
  sched <- ffscrapr::ff_schedule(mfl_conn) %>%
    dplyr::filter(week <= week_max) %>%
    dplyr::select(
      week, franchise_id, opponent_id,
      franchise_score, opponent_score, result
    )
  
  h2h_weekly <- sched %>%
    dplyr::group_by(franchise_id, week) %>%
    dplyr::summarise(
      h2h_wins_raw   = sum(franchise_score > opponent_score, na.rm = TRUE),
      h2h_ties_raw   = sum(franchise_score == opponent_score, na.rm = TRUE),
      h2h_losses_raw = sum(franchise_score < opponent_score, na.rm = TRUE),
      points_for     = sum(franchise_score, na.rm = TRUE),
      .groups = "drop"
    )
  
  # 3. Starters -> potential_points + O/D/ST/bench splits --------------
  starters <- ffscrapr::ff_starters(mfl_conn) %>%
    dplyr::filter(week <= week_max)
  
  weekly_pts_cats <- starters %>%
    dplyr::group_by(franchise_id, week) %>%
    dplyr::summarise(
      actual_from_starters = sum(
        player_score[starter_status == "starter"],
        na.rm = TRUE
      ),
      potential_points = sum(
        player_score[should_start == 1],
        na.rm = TRUE
      ),
      
      # Offense = starters only at offensive positions
      offense_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("QB", "RB", "WR", "TE")
        ],
        na.rm = TRUE
      ),
      
      # Defense = starters only at IDP positions
      defense_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("DT", "DE", "LB", "CB", "S")
        ],
        na.rm = TRUE
      ),
      
      # Special teams = starters only at PK/PN
      specialteams_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("PK", "PN")
        ],
        na.rm = TRUE
      ),
      
      # Bench = all nonstarters, regardless of position
      bench_points_week = sum(
        player_score[starter_status == "nonstarter"],
        na.rm = TRUE
      ),
      
      # Offense + special teams for starters only
      offst_points_week = sum(
        player_score[
          starter_status == "starter" &
            pos %in% c("QB", "RB", "WR", "TE", "PK", "PN")
        ],
        na.rm = TRUE
      ),
      
      .groups = "drop"
    )
  
  
  weekly_scores <- h2h_weekly %>%
    dplyr::left_join(weekly_pts_cats, by = c("franchise_id", "week"))
  
  # Sanity check: starter totals vs schedule totals --------------------
  mismatch <- weekly_scores %>%
    dplyr::filter(
      !is.na(actual_from_starters),
      abs(points_for - actual_from_starters) > 0.01
    ) %>%
    dplyr::left_join(franchises, by = "franchise_id")
  
  if (nrow(mismatch) > 0) {
    team_labels <- if ("franchise_name" %in% names(mismatch)) {
      paste0(
        "week ", mismatch$week,
        " – franchise_id ", mismatch$franchise_id,
        " (", mismatch$franchise_name, ")"
      )
    } else {
      paste0(
        "week ", mismatch$week,
        " – franchise_id ", mismatch$franchise_id
      )
    }
    
    warning(
      "Starter-based points differ from ff_schedule points for ",
      nrow(mismatch), " team-week rows: ",
      paste(team_labels, collapse = "; ")
    )
  }
  
  # 4. Weekly all-play wins (fast, rank-based) -------------------------
  n_teams <- weekly_scores %>%
    dplyr::summarise(n_teams = dplyr::n_distinct(franchise_id)) %>%
    dplyr::pull(n_teams)
  
  if (n_teams != 32L) {
    warning("Expected 32 teams, found ", n_teams,
            ". All-play logic assumes 32-team ADL.")
  }
  
  allplay_weekly <- weekly_scores %>%
    dplyr::group_by(week) %>%
    dplyr::group_modify(~ {
      tibble::tibble(
        franchise_id = .x$franchise_id,
        ap_wins_week = allplay_from_scores(.x$points_for)
      )
    }) %>%
    dplyr::ungroup()
  
  weekly_scores <- weekly_scores %>%
    dplyr::left_join(allplay_weekly, by = c("franchise_id", "week"))
  
  # 5. Bonus Games (W3 / W6 / W9 / W12 / Season) -----------------------
  calc_bonus_event <- function(weeks_vec, label) {
    weekly_scores %>%
      dplyr::filter(week %in% weeks_vec) %>%
      dplyr::group_by(franchise_id) %>%
      dplyr::summarise(
        ap_wins_seg    = sum(ap_wins_week,     na.rm = TRUE),
        points_seg     = sum(points_for,       na.rm = TRUE),
        pot_points_seg = sum(potential_points, na.rm = TRUE),
        .groups = "drop"
      ) %>%
      dplyr::arrange(
        dplyr::desc(ap_wins_seg),
        dplyr::desc(points_seg),
        dplyr::desc(pot_points_seg)
      ) %>%
      dplyr::mutate(
        seg_rank = dplyr::row_number(),
        bonus_result = dplyr::case_when(
          seg_rank <= 15L ~ 1,    # Bonus Win
          seg_rank <= 17L ~ 0.5,  # Bonus Tie
          TRUE            ~ 0     # Bonus Loss
        ),
        bonus_label = label
      ) %>%
      dplyr::select(franchise_id, bonus_label, bonus_result)
  }
  
  bonus_events <- list()
  if (week_max >= 3)  bonus_events[["W3"]]     <- calc_bonus_event(1:3,   "W3")
  if (week_max >= 6)  bonus_events[["W6"]]     <- calc_bonus_event(4:6,   "W6")
  if (week_max >= 9)  bonus_events[["W9"]]     <- calc_bonus_event(7:9,   "W9")
  if (week_max >= 12) {
    bonus_events[["W12"]]    <- calc_bonus_event(10:12, "W12")
    bonus_events[["SEASON"]] <- calc_bonus_event(1:12,  "SEASON")
  }
  
  if (length(bonus_events) == 0L) {
    # No bonus games awarded yet (week < 3)
    bonus_tbl <- franchises %>%
      dplyr::distinct(franchise_id) %>%
      dplyr::mutate(
        bonus_wins_raw   = 0,
        bonus_ties_raw   = 0,
        bonus_losses_raw = 0,
        bonus_wins       = 0
      )
  } else {
    bonus_tbl <- dplyr::bind_rows(bonus_events) %>%
      dplyr::group_by(franchise_id) %>%
      dplyr::summarise(
        bonus_wins_raw   = sum(bonus_result == 1,   na.rm = TRUE),
        bonus_ties_raw   = sum(bonus_result == 0.5, na.rm = TRUE),
        bonus_losses_raw = sum(bonus_result == 0,   na.rm = TRUE),
        bonus_wins       = sum(bonus_result,        na.rm = TRUE),
        .groups = "drop"
      )
  }
  
  # 6. Aggregate season-to-date standings -------------------------------
  h2h_season <- weekly_scores %>%
    dplyr::group_by(franchise_id) %>%
    dplyr::summarise(
      h2h_wins_raw     = sum(h2h_wins_raw,   na.rm = TRUE),
      h2h_ties_raw     = sum(h2h_ties_raw,   na.rm = TRUE),
      h2h_losses_raw   = sum(h2h_losses_raw, na.rm = TRUE),
      points_for       = sum(points_for,     na.rm = TRUE),
      potential_points = sum(potential_points, na.rm = TRUE),
      offense_points   = sum(offense_points_week,       na.rm = TRUE),
      defense_points   = sum(defense_points_week,       na.rm = TRUE),
      specialteams_points = sum(specialteams_points_week, na.rm = TRUE),
      bench_points     = sum(bench_points_week,         na.rm = TRUE),
      offst_points     = sum(offst_points_week,         na.rm = TRUE),
      ap_wins_total    = sum(ap_wins_week,   na.rm = TRUE),
      .groups = "drop"
    ) %>%
    dplyr::mutate(
      h2h_wins  = h2h_wins_raw + 0.5 * h2h_ties_raw,
      h2h_games = h2h_wins_raw + h2h_ties_raw + h2h_losses_raw
    )
  
  n_weeks_played    <- min(week_max, max(weekly_scores$week, na.rm = TRUE))
  ap_games_per_team <- (n_teams - 1L) * n_weeks_played
  
  standings <- h2h_season %>%
    dplyr::left_join(bonus_tbl, by = "franchise_id") %>%
    dplyr::mutate(
      bonus_wins_raw   = tidyr::replace_na(bonus_wins_raw,   0),
      bonus_ties_raw   = tidyr::replace_na(bonus_ties_raw,   0),
      bonus_losses_raw = tidyr::replace_na(bonus_losses_raw, 0),
      bonus_wins       = tidyr::replace_na(bonus_wins,       0),
      total_wins       = h2h_wins + bonus_wins,
      total_games      = h2h_games + (bonus_wins_raw + bonus_ties_raw + bonus_losses_raw),
      win_pct = dplyr::if_else(
        total_games > 0,
        total_wins / total_games,
        0
      ),
      ap_win_pct = if (ap_games_per_team > 0) {
        ap_wins_total / ap_games_per_team
      } else {
        0
      }
    ) %>%
    dplyr::left_join(franchises, by = "franchise_id") %>%
    dplyr::mutate(
      season       = season,
      through_week = week_max
    ) %>%
    dplyr::select(
      franchise_name,
      total_wins,
      ap_wins_total,
      points_for,
      potential_points,
      offense_points,
      defense_points,
      specialteams_points,
      bench_points,
      offst_points,
      
      h2h_wins_raw,
      h2h_losses_raw,
      h2h_ties_raw,
      h2h_wins,
      
      bonus_wins_raw,
      bonus_losses_raw,
      bonus_ties_raw,
      bonus_wins,
      
      dplyr::everything()
    )
  
  standings
}




###################################################################################################
## PLAYOFF SNAPSHOT: Add conference seeds, qual flags, and mini-league tiebreakers
##
## Input:
##   - standings: output from build_adl_weekly_results(), *single season*,
##                with columns like:
##                  season, through_week, conference, division,
##                  win_pct, ap_win_pct, points_for, etc.
##
## Output:
##   - standings with:
##       * qual flag ("y" division winner, "x" wild card, "" otherwise)
##       * playoff_seed (1–7 by conference)
##       * consol_seed  (8–16 by conference)
##       * seed         (playoff_seed or consol_seed)
##       * mini-league H2H tiebreak diagnostics for division leaders
###################################################################################################

add_adl_playoff_snapshot <- function(standings) {
  
  #-------------------------------
  # 0. Derive season, through_week, and MFL connection
  #-------------------------------
  season_vals <- unique(standings$season)
  if (length(season_vals) != 1L) {
    stop("standings must contain exactly one season; found: ",
         paste(season_vals, collapse = ", "))
  }
  season <- season_vals[[1]]
  
  week_vals    <- unique(standings$through_week)
  through_week <- max(week_vals, na.rm = TRUE)
  
  season_suffix <- substr(as.character(season), 3, 4)   # 2025 -> "25"
  conn_name     <- paste0("ADL", season_suffix)         # "ADL25"
  
  mfl_conn <- mfl_conns[[conn_name]]
  if (is.null(mfl_conn)) {
    stop("No MFL connection named ", conn_name, " found in load_mfl_conns().")
  }
  
  sched <- ffscrapr::ff_schedule(mfl_conn) %>%
    dplyr::filter(week <= through_week, week <= adl_max_week) %>%   # reg season weeks 1–12
    dplyr::select(
      week,
      franchise_id,
      opponent_id,
      franchise_score,
      opponent_score
    )
  
  #-------------------------------
  # 1. Helper: mini-league H2H for a tied group (division title)
  #-------------------------------
  compute_mini_h2h <- function(sched_tbl, team_ids) {
    if (length(team_ids) <= 1L) {
      return(
        tibble::tibble(
          franchise_id        = team_ids,
          h2h_mini_wins       = 0,
          h2h_mini_ties_raw   = 0,
          h2h_mini_losses_raw = 0,
          h2h_mini_pct        = NA_real_
        )
      )
    }
    
    sched_tbl %>%
      dplyr::filter(
        franchise_id %in% team_ids,
        opponent_id  %in% team_ids
      ) %>%
      dplyr::group_by(franchise_id) %>%
      dplyr::summarise(
        h2h_mini_wins_raw   = sum(franchise_score > opponent_score, na.rm = TRUE),
        h2h_mini_ties_raw   = sum(franchise_score == opponent_score, na.rm = TRUE),
        h2h_mini_losses_raw = sum(franchise_score < opponent_score, na.rm = TRUE),
        .groups = "drop"
      ) %>%
      dplyr::mutate(
        h2h_mini_wins  = h2h_mini_wins_raw + 0.5 * h2h_mini_ties_raw,
        h2h_mini_games = h2h_mini_wins_raw + h2h_mini_ties_raw + h2h_mini_losses_raw,
        h2h_mini_pct   = dplyr::if_else(
          h2h_mini_games > 0,
          h2h_mini_wins / h2h_mini_games,
          NA_real_
        )
      ) %>%
      dplyr::select(
        franchise_id,
        h2h_mini_wins,
        h2h_mini_losses_raw,
        h2h_mini_ties_raw,
        h2h_mini_pct
      )
  }
  
  #-------------------------------
  # 2. Attach mini-league H2H to division leaders' tie groups
  #-------------------------------
  standings_with_mini <- standings %>%
    dplyr::group_by(conference, division) %>%
    dplyr::group_modify(~ {
      div_tbl <- .x
      max_wp  <- max(div_tbl$win_pct, na.rm = TRUE)
      tied_ids <- div_tbl$franchise_id[div_tbl$win_pct == max_wp]
      
      mini_tbl <- compute_mini_h2h(sched_tbl = sched, team_ids = tied_ids)
      
      div_tbl %>%
        dplyr::left_join(mini_tbl, by = "franchise_id")
    }) %>%
    dplyr::ungroup()
  
  #-------------------------------
  # 3. Division winners (with mini-league tiebreaker)
  #    Tiebreakers:
  #      1. win_pct
  #      2. h2h_mini_pct
  #      3. ap_win_pct
  #      4. points_for
  #-------------------------------
  division_winners <- standings_with_mini %>%
    dplyr::group_by(conference, division) %>%
    dplyr::arrange(
      dplyr::desc(win_pct),
      dplyr::desc(h2h_mini_pct),
      dplyr::desc(ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::slice(1) %>%
    dplyr::ungroup() %>%
    dplyr::transmute(
      franchise_id,
      is_division_winner = TRUE
    )
  
  #-------------------------------
  # 4. Wild cards (no mini-league in bylaws)
  #-------------------------------
  wild_cards <- standings_with_mini %>%
    dplyr::anti_join(division_winners, by = "franchise_id") %>%
    dplyr::group_by(conference) %>%
    dplyr::arrange(
      dplyr::desc(win_pct),
      dplyr::desc(ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::mutate(wc_rank = dplyr::row_number()) %>%
    dplyr::filter(wc_rank <= 3L) %>%
    dplyr::ungroup() %>%
    dplyr::transmute(
      franchise_id,
      is_wild_card = TRUE
    )
  
  #-------------------------------
  # 5. Merge flags and compute qual + seeds
  #-------------------------------
  standings_flagged <- standings_with_mini %>%
    dplyr::left_join(division_winners, by = "franchise_id") %>%
    dplyr::left_join(wild_cards,        by = "franchise_id") %>%
    dplyr::mutate(
      is_division_winner = tidyr::replace_na(is_division_winner, FALSE),
      is_wild_card       = tidyr::replace_na(is_wild_card, FALSE),
      is_playoff_team    = is_division_winner | is_wild_card,
      qual = dplyr::case_when(
        is_division_winner ~ "y",
        is_wild_card       ~ "x",
        TRUE               ~ ""
      )
    )
  
  playoff_teams <- standings_flagged %>%
    dplyr::filter(is_playoff_team)
  
  non_playoff_teams <- standings_flagged %>%
    dplyr::filter(!is_playoff_team)
  
  # Playoff seeding (1–7) by AP then points (ADL seeding)
  playoff_seeds <- playoff_teams %>%
    dplyr::group_by(conference) %>%
    dplyr::arrange(
      dplyr::desc(ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::mutate(playoff_seed = dplyr::row_number()) %>%
    dplyr::ungroup()
  
  # Consolation seeding (8–16)
  consolation_seeds <- non_playoff_teams %>%
    dplyr::group_by(conference) %>%
    dplyr::arrange(
      dplyr::desc(ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::mutate(consol_seed = dplyr::row_number() + 7L) %>%
    dplyr::ungroup()
  
  combined <- dplyr::bind_rows(playoff_seeds, consolation_seeds) %>%
    dplyr::mutate(
      seed = dplyr::case_when(
        is_playoff_team ~ playoff_seed,
        TRUE            ~ consol_seed
      )
    )
  
  #-------------------------------
  # 6. Final column ordering
  #-------------------------------
  combined %>%
    dplyr::arrange(conference, seed) %>%
    dplyr::select(
      # First two columns:
      qual,        # "y", "x", or ""
      seed,          # 1–16 conference seed
      
      # Main stats:
      franchise_name,
      total_wins,
      ap_wins_total,
      points_for,
      potential_points,
      offense_points,
      defense_points,
      specialteams_points,
      bench_points,
      offst_points,
      
      # Raw + adjusted H2H:
      h2h_wins_raw,
      h2h_losses_raw,
      h2h_ties_raw,
      h2h_wins,
      
      # Raw + adjusted Bonus:
      bonus_wins_raw,
      bonus_losses_raw,
      bonus_ties_raw,
      bonus_wins,
      
      # Mini-league diagnostics:
      h2h_mini_wins,
      h2h_mini_losses_raw,
      h2h_mini_ties_raw,
      h2h_mini_pct,
      
      # Playoff vs consolation seeds:
      playoff_seed,
      consol_seed,
      
      # Everything else (conference, division, win_pct, ids, etc.)
      dplyr::everything()
    )
}



###############################################################################################
## POINTS-BASED MONTE CARLO ENGINE
##
## Goal:
##   Use historical weekly data to build a *points model* for each team at a snapshot week:
##     - Choose how to model the **mean** weekly points going forward
##     - Choose how to model the **standard deviation** (volatility)
##   Then simulate the remaining schedule many times, to get:
##     - Expected remaining points
##     - Expected remaining H2H wins
##     - Distribution quantiles for remaining points
##
## This replaces the previous “many linear models for AP/H2H” section.
###############################################################################################

###################################################################################################
## build_points_params_from_history()
##
## Purpose (DIAGNOSTICS ONLY, NO CHOOSING):
##   Using ADL weekly history, this function:
##
##   1) For each snapshot week w (1..max_week-1), builds 5 models to predict
##      EACH TEAM’S *remaining mean weekly points_for* over weeks (w+1..max_week),
##      using predictors available at week w:
##
##        Target:
##          rem_mean_pts = (season_points_for_total - points_for_to_date) /
##                         (max_week - w)
##
##        Candidate models:
##          M1: rem_mean_pts ~ ap_win_pct            # AP-only (renamed)
##          M2: rem_mean_pts ~ avg_pf                # PF-only (renamed)
##          M3: rem_mean_pts ~ avg_pot               # Pot-only (renamed)
##          M4: rem_mean_pts ~ avg_pf + avg_pot      # PF + Pot
##          M5: rem_mean_pts ~ avg_pf + avg_pot + ap_win_pct   # PF + Pot + AP
##
##        where:
##          avg_pf  = points_for       / w
##          avg_pot = potential_points / w
##
##      It returns a tibble of adjusted R² for all 5 models by week,
##      AND a ggplot of adj. R² vs week (5 lines).
##
##   2) For standard deviation of points:
##        - For each SEASON:
##             * compute each team’s SD of points_for_week across the full season
##             * average those SDs across teams -> avg_sd_pts_per_season
##        - Then compute an overall average SD across all season-team combos.
##
## Inputs:
##   - history_df: output from build_adl_weekly_history()
##                 must contain:
##                   season, week, franchise_id,
##                   points_for_week, potential_points_week,
##                   points_for, potential_points, ap_win_pct
##   - max_week:   final regular-season week (ADL: 12 / adl_max_week)
##   - min_rows_per_week: if fewer rows than this, we skip that week (NA adj.R²)
##
## Output:
##   A list with:
##     $mean_model_comparison : tibble(week, m1_ap_adjR2, m2_pf_adjR2, m3_pot_adjR2,
##                                           m4_pf_pot_adjR2, m5_pf_pot_ap_adjR2)
##     $mean_model_plot       : ggplot object (adj.R² vs week for 5 models, labeled M1–M5)
##     $coefficients_m4       : tibble(week, pf_coef, pot_coef)  # NEW per your request
##     $sd_by_season          : tibble(season, avg_sd_pts)
##     $overall_sd_avg        : single numeric, overall mean SD
##
##   This function DOES NOT choose a model or SD – it just reports diagnostics.
###################################################################################################


build_points_params_from_history <- function(history_df, max_week = 12) {
  # ----------------------------------------------------------
  # 0) Prep: final season totals for points_for
  # ----------------------------------------------------------
  season_totals <- history_df %>%
    dplyr::filter(week == max_week) %>%
    dplyr::select(season, franchise_id, season_points_for = points_for)
  
  weeks_to_test <- 1:(max_week - 1L)
  
  # ----------------------------------------------------------
  # 1) MEAN (POINTS) MODELS: 5 models, adj.R² by week
  #    M1: PF
  #    M2: Off + Def + ST + Bench
  #    M3: Pot
  #    M4: PF + Pot
  #    M5: Off + Def + ST + Pot
  # ----------------------------------------------------------
  
  mean_results <- purrr::map(weeks_to_test, function(wk) {
    wk_df <- history_df %>%
      dplyr::filter(week == wk) %>%
      dplyr::left_join(season_totals, by = c("season", "franchise_id")) %>%
      dplyr::mutate(
        rem_pts      = season_points_for - points_for,
        rem_weeks    = max_week - wk,
        ppg          = points_for       / wk,
        pot_ppg      = potential_points / wk,
        off_ppg      = offense_points_week       / 1,  # weekly already
        def_ppg      = defense_points_week       / 1,
        st_ppg       = specialteams_points_week  / 1,
        bench_ppg    = bench_points_week         / 1,
        offst_ppg    = offst_points_week         / 1
      ) %>%
      dplyr::filter(
        !is.na(rem_pts),
        rem_weeks > 0,
        !is.na(ppg),
        !is.na(pot_ppg)
      ) %>%
      dplyr::mutate(
        rem_mean_pts = rem_pts / rem_weeks
      )
    
    if (nrow(wk_df) < 10) {
      comp_row <- tibble::tibble(
        week                    = wk,
        m1_pf_adjR2             = NA_real_,
        m2_off_def_st_bench_adjR2 = NA_real_,
        m3_pot_adjR2            = NA_real_,
        m4_pf_pot_adjR2         = NA_real_,
        m5_off_def_st_pot_adjR2 = NA_real_
      )
      m4_row <- tibble::tibble(
        week         = wk,
        m4_intercept = NA_real_,
        m4_pf_coef   = NA_real_,
        m4_pot_coef  = NA_real_
      )
      return(list(comparison = comp_row, m4_coefs = m4_row))
    }
    
    # M1: PF only
    mod1 <- lm(rem_mean_pts ~ ppg, data = wk_df)
    s1   <- summary(mod1)
    m1_adjR2 <- s1$adj.r.squared
    
    # M2: Off + Def + ST + Bench
    mod2 <- lm(rem_mean_pts ~ off_ppg + def_ppg + st_ppg + bench_ppg, data = wk_df)
    s2   <- summary(mod2)
    m2_adjR2 <- s2$adj.r.squared
    
    # M3: Pot only
    mod3 <- lm(rem_mean_pts ~ pot_ppg, data = wk_df)
    s3   <- summary(mod3)
    m3_adjR2 <- s3$adj.r.squared
    
    # M4: PF + Pot
    mod4 <- lm(rem_mean_pts ~ ppg + pot_ppg, data = wk_df)
    s4   <- summary(mod4)
    m4_adjR2 <- s4$adj.r.squared
    c4 <- coef(s4)
    m4_intercept <- c4["(Intercept)", "Estimate"]
    m4_pf_coef   <- c4["ppg",         "Estimate"]
    m4_pot_coef  <- c4["pot_ppg",     "Estimate"]
    
    # M5: Off + Def + ST + Pot
    mod5 <- lm(rem_mean_pts ~ off_ppg + def_ppg + st_ppg + pot_ppg, data = wk_df)
    s5   <- summary(mod5)
    m5_adjR2 <- s5$adj.r.squared
    
    comp_row <- tibble::tibble(
      week                       = wk,
      m1_pf_adjR2                = m1_adjR2,
      m2_off_def_st_bench_adjR2  = m2_adjR2,
      m3_pot_adjR2               = m3_adjR2,
      m4_pf_pot_adjR2            = m4_adjR2,
      m5_off_def_st_pot_adjR2    = m5_adjR2
    )
    
    m4_row <- tibble::tibble(
      week         = wk,
      m4_intercept = m4_intercept,
      m4_pf_coef   = m4_pf_coef,
      m4_pot_coef  = m4_pot_coef
    )
    
    list(comparison = comp_row, m4_coefs = m4_row)
  })
  
  mean_model_comparison <- purrr::map_dfr(mean_results, "comparison")
  m4_coefs_by_week      <- purrr::map_dfr(mean_results, "m4_coefs")
  
  # ----------------------------------------------------------
  # 1b) Mean-model plot (M1–M5 adj.R² vs week)
  # ----------------------------------------------------------
  mean_model_plot <- mean_model_comparison %>%
    tidyr::pivot_longer(
      cols = dplyr::starts_with("m"),
      names_to = "model",
      values_to = "adjR2"
    ) %>%
    dplyr::mutate(
      model = factor(
        model,
        levels = c(
          "m1_pf_adjR2",
          "m2_off_def_st_bench_adjR2",
          "m3_pot_adjR2",
          "m4_pf_pot_adjR2",
          "m5_off_def_st_pot_adjR2"
        ),
        labels = c(
          "M1: Points For",
          "M2: Off + Def + ST + Bench",
          "M3: Potential Pts",
          "M4: PF + Pot",
          "M5: Off + Def + ST + Pot"
        )
      )
    ) %>%
    ggplot2::ggplot(ggplot2::aes(x = week, y = adjR2, color = model)) +
    ggplot2::geom_line(size = 1) +
    ggplot2::geom_point(size = 2) +
    ggplot2::labs(
      title = "Adjusted R² by Week for Points-Mean Models",
      x     = "Week (snapshot)",
      y     = "Adjusted R²",
      color = "Model"
    ) +
    ggplot2::theme_minimal(base_size = 13) +
    ggplot2::theme(
      legend.position = "right",
      legend.title    = ggplot2::element_text(size = 12, face = "bold"),
      legend.text     = ggplot2::element_text(size = 11)
    )
  
  # ----------------------------------------------------------
  # 1c) Week 6 mean models: store lm objects for quick comparison
  # ----------------------------------------------------------
  week6_points_models <- NULL
  wk6 <- 6L
  
  if (wk6 < max_week) {
    wk6_df <- history_df %>%
      dplyr::filter(week == wk6) %>%
      dplyr::left_join(season_totals, by = c("season", "franchise_id")) %>%
      dplyr::mutate(
        rem_pts      = season_points_for - points_for,
        rem_weeks    = max_week - wk6,
        ppg          = points_for       / wk6,
        pot_ppg      = potential_points / wk6,
        off_ppg      = offense_points_week       / 1,
        def_ppg      = defense_points_week       / 1,
        st_ppg       = specialteams_points_week  / 1,
        bench_ppg    = bench_points_week         / 1
      ) %>%
      dplyr::filter(
        !is.na(rem_pts),
        rem_weeks > 0,
        !is.na(ppg),
        !is.na(pot_ppg)
      ) %>%
      dplyr::mutate(
        rem_mean_pts = rem_pts / rem_weeks
      )
    
    if (nrow(wk6_df) >= 10) {
      m1 <- lm(rem_mean_pts ~ ppg, data = wk6_df)
      m2 <- lm(rem_mean_pts ~ off_ppg + def_ppg + st_ppg + bench_ppg, data = wk6_df)
      m3 <- lm(rem_mean_pts ~ pot_ppg, data = wk6_df)
      m4 <- lm(rem_mean_pts ~ ppg + pot_ppg, data = wk6_df)
      m5 <- lm(rem_mean_pts ~ off_ppg + def_ppg + st_ppg + pot_ppg, data = wk6_df)
      
      week6_points_models <- list(
        M1_PF              = m1,
        M2_Off_Def_ST_Bench= m2,
        M3_Pot             = m3,
        M4_PF_Pot          = m4,
        M5_Off_Def_ST_Pot  = m5
      )
    }
  }
  
  # ----------------------------------------------------------
  # 2) SD MODELS: 4 models for sd of future points, adj.R² by week
  #    S1: SD(rem) ~ SD(so far)
  #    S2: SD(rem) ~ SD(so far) + PPG
  #    S3: SD(rem) ~ SD(so far) + Off PPG
  #    S4: SD(rem) ~ SD(so far) + Pot PPG
  # ----------------------------------------------------------
  
  sd_results <- purrr::map(weeks_to_test, function(wk) {
    sd_df <- history_df %>%
      dplyr::filter(week <= max_week) %>%
      dplyr::group_by(season, franchise_id) %>%
      dplyr::summarise(
        sd_so_far       = stats::sd(points_for_week[week <= wk], na.rm = TRUE),
        sd_rem_ppg      = stats::sd(points_for_week[week > wk & week <= max_week], na.rm = TRUE),
        ppg_so_far      = mean(points_for_week[week <= wk], na.rm = TRUE),
        off_ppg_so_far  = mean(offense_points_week[week <= wk], na.rm = TRUE),
        pot_ppg_so_far  = mean(potential_points_week[week <= wk], na.rm = TRUE),
        .groups = "drop"
      ) %>%
      dplyr::filter(
        !is.na(sd_so_far),
        !is.na(sd_rem_ppg)
      )
    
    if (nrow(sd_df) < 10) {
      return(tibble::tibble(
        week                 = wk,
        s1_sd_only_adjR2     = NA_real_,
        s2_sd_ppg_adjR2      = NA_real_,
        s3_sd_off_adjR2      = NA_real_,
        s4_sd_pot_adjR2      = NA_real_
      ))
    }
    
    s1 <- summary(lm(sd_rem_ppg ~ sd_so_far, data = sd_df))
    s2 <- summary(lm(sd_rem_ppg ~ sd_so_far + ppg_so_far, data = sd_df))
    s3 <- summary(lm(sd_rem_ppg ~ sd_so_far + off_ppg_so_far, data = sd_df))
    s4 <- summary(lm(sd_rem_ppg ~ sd_so_far + pot_ppg_so_far, data = sd_df))
    
    tibble::tibble(
      week                 = wk,
      s1_sd_only_adjR2     = s1$adj.r.squared,
      s2_sd_ppg_adjR2      = s2$adj.r.squared,
      s3_sd_off_adjR2      = s3$adj.r.squared,
      s4_sd_pot_adjR2      = s4$adj.r.squared
    )
  })
  
  sd_model_comparison <- purrr::map_dfr(sd_results, ~ .x)
  
  # ----------------------------------------------------------
  # 2b) Week 6 SD models: store lm objects for quick comparison
  # ----------------------------------------------------------
  week6_sd_models <- NULL
  
  if (wk6 < max_week) {
    sd6_df <- history_df %>%
      dplyr::filter(week <= max_week) %>%
      dplyr::group_by(season, franchise_id) %>%
      dplyr::summarise(
        sd_so_far       = stats::sd(points_for_week[week <= wk6], na.rm = TRUE),
        sd_rem_ppg      = stats::sd(points_for_week[week > wk6 & week <= max_week], na.rm = TRUE),
        ppg_so_far      = mean(points_for_week[week <= wk6], na.rm = TRUE),
        off_ppg_so_far  = mean(offense_points_week[week <= wk6], na.rm = TRUE),
        pot_ppg_so_far  = mean(potential_points_week[week <= wk6], na.rm = TRUE),
        .groups = "drop"
      ) %>%
      dplyr::filter(
        !is.na(sd_so_far),
        !is.na(sd_rem_ppg)
      )
    
    if (nrow(sd6_df) >= 10) {
      s1 <- lm(sd_rem_ppg ~ sd_so_far, data = sd6_df)
      s2 <- lm(sd_rem_ppg ~ sd_so_far + ppg_so_far, data = sd6_df)
      s3 <- lm(sd_rem_ppg ~ sd_so_far + off_ppg_so_far, data = sd6_df)
      s4 <- lm(sd_rem_ppg ~ sd_so_far + pot_ppg_so_far, data = sd6_df)
      
      week6_sd_models <- list(
        S1_SD_Only   = s1,
        S2_SD_PPG    = s2,
        S3_SD_OffPPG = s3,
        S4_SD_PotPPG = s4
      )
    }
  }
  
  # ----------------------------------------------------------
  # 3) SD diagnostics: per-season and overall SD of points_for_week
  # ----------------------------------------------------------
  sd_by_season <- history_df %>%
    dplyr::filter(week <= max_week) %>%
    dplyr::group_by(season, franchise_id) %>%
    dplyr::summarise(
      points_sd = stats::sd(points_for_week, na.rm = TRUE),
      .groups   = "drop"
    ) %>%
    dplyr::group_by(season) %>%
    dplyr::summarise(
      avg_points_sd = mean(points_sd, na.rm = TRUE),
      n_teams       = dplyr::n(),
      .groups       = "drop"
    )
  
  overall_sd_avg <- mean(sd_by_season$avg_points_sd, na.rm = TRUE)
  
  # ----------------------------------------------------------
  # 4) Return everything
  # ----------------------------------------------------------
  list(
    mean_model_comparison = mean_model_comparison,
    mean_model_plot       = mean_model_plot,
    m4_coefs_by_week      = m4_coefs_by_week,
    sd_model_comparison   = sd_model_comparison,
    sd_by_season          = sd_by_season,
    overall_sd_avg        = overall_sd_avg,
    week6_points_models   = week6_points_models,
    week6_sd_models       = week6_sd_models
  )
}



###################################################################################################
## run_adl_monte_carlo()
##
## Purpose:
##   For a given ADL season + snapshot week, simulate the REMAINDER of the regular season
##   using:
##     - Mean model:   M3 (avg_pot only) from historical seasons
##     - SD of points: sd_points (e.g. points_diag$overall_sd_avg)
##     - n_sims:       number of Monte Carlo runs (e.g. 3000)
##
##   For each sim, it:
##     1) Simulates weekly points_for for each team for weeks (through_week+1 .. max_week)
##     2) Derives weekly all-play wins and H2H wins from those simulated scores
##     3) Recomputes all 5 bonus events (Q1, Q2, Q3, Q4, RS) using:
##          - actual scores for past weeks
##          - simulated scores for future weeks
##
##   It then aggregates across sims to produce EXPECTED values:
##     - Expected remaining AP wins + final AP wins
##     - Expected remaining H2H wins + final H2H wins
##     - Expected Q1, Q2, Q3, Q4, RS bonus wins
##     - Expected weekly H2H wins: pred_w1_wins ... pred_w12_wins
##
## Inputs:
##   - standings_df : output from build_adl_weekly_results(season, week)
##                    must include:
##                      season, through_week, franchise_id,
##                      ap_wins_total, h2h_wins, total_wins,
##                      points_for, potential_points,
##                      franchise_name, conference, division
##   - history_df   : output from build_adl_weekly_history() for MULTIPLE seasons
##                    (used as training data for M3 mean model)
##   - sched_df     : ff_schedule() for the CURRENT season, with:
##                      week, franchise_id, opponent_id
##   - sd_points    : scalar SD for weekly points_for (e.g. points_diag$overall_sd_avg)
##   - max_week     : final regular-season week (ADL: 12)
##   - n_sims       : number of Monte Carlo simulations
##
## Output:
##   A list:
##     $team_summary : one row per team with:
##                      franchise_id, franchise_name, conference, division,
##                      actual_* columns (through snapshot week),
##                      predicted_* columns (expected future + final)
##     $weekly_h2h   : tibble(franchise_id, week, pred_weekly_h2h for each week)
##     $bonus_expect : tibble(franchise_id, pred_Q1_bonus, ..., pred_RS_bonus)
##     $mean_model_m3: the fitted M3 mean model (rem_mean_pts ~ avg_pot)
##
## Notes:
##   - Uses progressr for a text progress bar if available:
##       install.packages("progressr")
###################################################################################################



###################################################################################################
## FAST, STREAMING MONTE CARLO ENGINE
##
## Same interface as before:
##   run_adl_monte_carlo(standings_df, history_df, sched_df, sd_points, max_week = 12L, n_sims = 3000L)
##
## Returns:
##   $team_summary : tibble with actual + expected future wins and bonus
##   $weekly_h2h   : tibble(franchise_id, pred_w1, ..., pred_w12)
##   $bonus_expect : tibble(franchise_id, pred_Q1_bonus, ..., pred_RS_bonus)
##   $mean_model_m3: fitted M3 mean model (rem_mean_pts ~ avg_pot)
##
## Changes vs old version:
##   - Uses allplay_from_scores() (no Cartesian product).
##   - Uses base matrices for simulated points & bonus segments.
##   - Aggregates expectations inside the loop (no giant bind_rows).
##   - Adds exp_rem_bonus_wins to team_summary.
###################################################################################################

run_adl_monte_carlo <- function(
    standings_df,
    history_df,
    sched_df,
    sd_points,
    max_week = 12L,
    n_sims   = 3000L
) {
  
  #-------------------------------------------------------
  # 0. Basic checks: one season, one through_week
  #-------------------------------------------------------
  season_vals <- unique(standings_df$season)
  if (length(season_vals) != 1L) {
    stop("standings_df must contain exactly one season.")
  }
  season0 <- season_vals[[1]]
  
  wk_vals <- unique(standings_df$through_week)
  if (length(wk_vals) != 1L) {
    stop("standings_df must contain exactly one through_week.")
  }
  wk0 <- wk_vals[[1]]
  
  if (wk0 >= max_week) {
    stop("Snapshot week is already at or beyond max_week; nothing to simulate.")
  }
  
  future_weeks    <- seq.int(wk0 + 1L, max_week)
  n_future_weeks  <- length(future_weeks)
  
  #-------------------------------------------------------
  # 1. Fit the M3 (avg_pot only) mean model at week wk0
  #    using fully-completed seasons in history_df
  #-------------------------------------------------------
  full_seasons <- history_df %>%
    dplyr::filter(week == max_week) %>%
    dplyr::distinct(season) %>%
    dplyr::pull(season)
  
  train_seasons <- setdiff(full_seasons, season0)
  if (length(train_seasons) == 0L) {
    stop("No fully-completed prior seasons available for training mean model.")
  }
  
  season_totals <- history_df %>%
    dplyr::filter(season %in% train_seasons, week == max_week) %>%
    dplyr::select(season, franchise_id, season_pts = points_for)
  
  snapshot_train <- history_df %>%
    dplyr::filter(season %in% train_seasons, week == wk0) %>%
    dplyr::select(
      season, franchise_id,
      pts_to_date = points_for,
      pot_to_date = potential_points
    )
  
  train_df <- snapshot_train %>%
    dplyr::inner_join(season_totals, by = c("season", "franchise_id")) %>%
    dplyr::mutate(
      rem_weeks    = max_week - wk0,
      rem_mean_pts = (season_pts - pts_to_date) / rem_weeks,
      avg_pot      = pot_to_date / wk0
    ) %>%
    dplyr::filter(rem_weeks > 0)
  
  if (nrow(train_df) < 10L) {
    stop("Not enough training rows to fit M3 mean model at week ", wk0, ".")
  }
  
  mean_mod_m3 <- stats::lm(rem_mean_pts ~ avg_pot, data = train_df)
  a3 <- stats::coef(mean_mod_m3)[["(Intercept)"]]
  b3 <- stats::coef(mean_mod_m3)[["avg_pot"]]
  
  #-------------------------------------------------------
  # 2. Current-season snapshot: compute mu (mean) per team
  #-------------------------------------------------------
  curr_teams <- standings_df %>%
    dplyr::select(
      season,
      through_week,
      franchise_id,
      franchise_name,
      conference,
      division,
      ap_wins_total,
      h2h_wins,
      total_wins,
      bonus_wins,
      points_for,
      potential_points
    ) %>%
    dplyr::mutate(
      avg_pf       = points_for       / through_week,
      avg_pot      = potential_points / through_week,
      rem_weeks    = max_week - through_week,
      rem_mean_hat = a3 + b3 * avg_pot,
      mu_pts       = pmax(rem_mean_hat, 0)
    )
  
  team_ids   <- curr_teams$franchise_id
  n_teams    <- length(team_ids)
  team_index <- seq_len(n_teams)
  names(team_index) <- team_ids
  
  #-------------------------------------------------------
  # 3. Actual weekly scores and AP/H2H for current season
  #-------------------------------------------------------
  hist_season <- history_df %>%
    dplyr::filter(season == season0, week <= wk0)
  
  # Points / AP / H2H matrices: rows = teams, cols = weeks 1..wk0
  pts_mat_actual <- matrix(0, nrow = n_teams, ncol = wk0)
  ap_mat_actual  <- matrix(0, nrow = n_teams, ncol = wk0)
  h2h_mat_actual <- matrix(0, nrow = n_teams, ncol = wk0)
  
  if (wk0 > 0L && nrow(hist_season) > 0L) {
    for (row_i in seq_len(nrow(hist_season))) {
      w  <- hist_season$week[row_i]
      id <- hist_season$franchise_id[row_i]
      idx <- team_index[[as.character(id)]]
      
      pts_mat_actual[idx, w] <- hist_season$points_for_week[row_i]
      ap_mat_actual[idx,  w] <- hist_season$ap_wins_week[row_i]
      
      h2h_val <- hist_season$h2h_wins_week_raw[row_i] +
        0.5 * hist_season$h2h_ties_week_raw[row_i]
      h2h_mat_actual[idx, w] <- h2h_val
    }
  }
  
  #-------------------------------------------------------
  # 4. Remaining schedule in index form for fast H2H calc
  #    IMPORTANT: dedupe games (ff_schedule() lists each game twice)
  #-------------------------------------------------------
  sched_rem <- sched_df %>%
    dplyr::filter(week > wk0, week <= max_week) %>%
    # Normalize matchup so each game appears only once
    dplyr::mutate(
      t1 = pmin(franchise_id, opponent_id),
      t2 = pmax(franchise_id, opponent_id)
    ) %>%
    dplyr::distinct(week, t1, t2, .keep_all = TRUE) %>%
    dplyr::transmute(
      week,
      i   = team_index[as.character(t1)],
      j   = team_index[as.character(t2)],
      col = week - wk0
    )
  
  sched_rem_mat <- as.data.frame(sched_rem)
  
  #-------------------------------------------------------
  # 5. Initialize accumulators for expectations
  #-------------------------------------------------------
  accum_rem_ap   <- numeric(n_teams)
  accum_rem_h2h  <- numeric(n_teams)
  accum_bonus_Q1 <- numeric(n_teams)
  accum_bonus_Q2 <- numeric(n_teams)
  accum_bonus_Q3 <- numeric(n_teams)
  accum_bonus_Q4 <- numeric(n_teams)
  accum_bonus_RS <- numeric(n_teams)
  
  weekly_future_h2h_sum <- matrix(0, nrow = n_teams, ncol = n_future_weeks)
  
  pb <- utils::txtProgressBar(min = 0, max = n_sims, style = 3)
  
  #-------------------------------------------------------
  # 6. Run simulations
  #-------------------------------------------------------
  for (sim_id in seq_len(n_sims)) {
    
    # 6a. Simulate future weekly points (n_teams x n_future_weeks)
    pts_future <- matrix(
      stats::rnorm(
        n_teams * n_future_weeks,
        mean = rep(curr_teams$mu_pts, times = n_future_weeks),
        sd   = sd_points
      ),
      nrow = n_teams,
      ncol = n_future_weeks,
      byrow = FALSE
    )
    pts_future[pts_future < 0] <- 0
    
    # 6b. All-play wins for future weeks (fast, rank-based)
    ap_future <- matrix(0, nrow = n_teams, ncol = n_future_weeks)
    if (n_future_weeks > 0L) {
      for (c in seq_len(n_future_weeks)) {
        ap_future[, c] <- allplay_from_scores(pts_future[, c])
      }
    }
    
    # 6c. H2H weekly results for future weeks
    rem_h2h_sim    <- numeric(n_teams)
    weekly_h2h_sim <- matrix(0, nrow = n_teams, ncol = n_future_weeks)
    
    if (nrow(sched_rem_mat) > 0L) {
      for (g in seq_len(nrow(sched_rem_mat))) {
        i   <- sched_rem_mat$i[g]
        j   <- sched_rem_mat$j[g]
        col <- sched_rem_mat$col[g]
        
        pi <- pts_future[i, col]
        pj <- pts_future[j, col]
        
        if (pi > pj) {
          ri <- 1;   rj <- 0
        } else if (pi < pj) {
          ri <- 0;   rj <- 1
        } else {
          ri <- 0.5; rj <- 0.5
        }
        
        rem_h2h_sim[i] <- rem_h2h_sim[i] + ri
        rem_h2h_sim[j] <- rem_h2h_sim[j] + rj
        
        weekly_h2h_sim[i, col] <- weekly_h2h_sim[i, col] + ri
        weekly_h2h_sim[j, col] <- weekly_h2h_sim[j, col] + rj
      }
    }
    
    # 6d. Full-season matrices for bonus segments
    pts_mat_sim <- cbind(pts_mat_actual, pts_future)
    ap_mat_sim  <- cbind(ap_mat_actual,  ap_future)
    
    # Segment AP and points
    seg_Q1_ap  <- rowSums(ap_mat_sim[, 1:3,   drop = FALSE])
    seg_Q2_ap  <- rowSums(ap_mat_sim[, 4:6,   drop = FALSE])
    seg_Q3_ap  <- rowSums(ap_mat_sim[, 7:9,   drop = FALSE])
    seg_Q4_ap  <- rowSums(ap_mat_sim[, 10:12, drop = FALSE])
    seg_RS_ap  <- rowSums(ap_mat_sim[, 1:12,  drop = FALSE])
    
    seg_Q1_pts <- rowSums(pts_mat_sim[, 1:3,   drop = FALSE])
    seg_Q2_pts <- rowSums(pts_mat_sim[, 4:6,   drop = FALSE])
    seg_Q3_pts <- rowSums(pts_mat_sim[, 7:9,   drop = FALSE])
    seg_Q4_pts <- rowSums(pts_mat_sim[, 10:12, drop = FALSE])
    seg_RS_pts <- rowSums(pts_mat_sim[, 1:12,  drop = FALSE])
    
    Q1_bonus <- bonus_from_segment(seg_Q1_ap, seg_Q1_pts)
    Q2_bonus <- bonus_from_segment(seg_Q2_ap, seg_Q2_pts)
    Q3_bonus <- bonus_from_segment(seg_Q3_ap, seg_Q3_pts)
    Q4_bonus <- bonus_from_segment(seg_Q4_ap, seg_Q4_pts)
    RS_bonus <- bonus_from_segment(seg_RS_ap, seg_RS_pts)
    
    # 6e. Update accumulators
    accum_rem_ap   <- accum_rem_ap   + rowSums(ap_future)
    accum_rem_h2h  <- accum_rem_h2h  + rem_h2h_sim
    accum_bonus_Q1 <- accum_bonus_Q1 + Q1_bonus
    accum_bonus_Q2 <- accum_bonus_Q2 + Q2_bonus
    accum_bonus_Q3 <- accum_bonus_Q3 + Q3_bonus
    accum_bonus_Q4 <- accum_bonus_Q4 + Q4_bonus
    accum_bonus_RS <- accum_bonus_RS + RS_bonus
    
    weekly_future_h2h_sum <- weekly_future_h2h_sum + weekly_h2h_sim
    
    utils::setTxtProgressBar(pb, sim_id)
  }
  
  close(pb)
  
  #-------------------------------------------------------
  # 7. Convert accumulators to expectations
  #-------------------------------------------------------
  exp_rem_ap_wins  <- accum_rem_ap  / n_sims
  exp_rem_h2h_wins <- accum_rem_h2h / n_sims
  
  pred_Q1_bonus <- accum_bonus_Q1 / n_sims
  pred_Q2_bonus <- accum_bonus_Q2 / n_sims
  pred_Q3_bonus <- accum_bonus_Q3 / n_sims
  pred_Q4_bonus <- accum_bonus_Q4 / n_sims
  pred_RS_bonus <- accum_bonus_RS / n_sims
  
  # Weekly H2H expectations for future weeks
  weekly_future_exp <- weekly_future_h2h_sum / n_sims
  
  # Build full weekly H2H matrix (1..max_week)
  weekly_h2h_all <- matrix(0, nrow = n_teams, ncol = max_week)
  if (wk0 > 0L) {
    weekly_h2h_all[, 1:wk0] <- h2h_mat_actual
  }
  if (n_future_weeks > 0L) {
    weekly_h2h_all[, (wk0 + 1L):max_week] <- weekly_future_exp
  }
  
  weekly_h2h_df <- as.data.frame(weekly_h2h_all)
  colnames(weekly_h2h_df) <- paste0("pred_w", seq_len(max_week), "_wins")
  
  weekly_h2h <- tibble::tibble(franchise_id = team_ids) %>%
    dplyr::bind_cols(weekly_h2h_df)
  
  # Bonus expectations tibble
  bonus_expect <- tibble::tibble(
    franchise_id  = team_ids,
    pred_Q1_bonus = pred_Q1_bonus,
    pred_Q2_bonus = pred_Q2_bonus,
    pred_Q3_bonus = pred_Q3_bonus,
    pred_Q4_bonus = pred_Q4_bonus,
    pred_RS_bonus = pred_RS_bonus
  )
  
  #-------------------------------------------------------
  # 8. Build final TEAM SUMMARY table
  #-------------------------------------------------------
  agg_df <- tibble::tibble(
    franchise_id     = team_ids,
    exp_rem_ap_wins  = exp_rem_ap_wins,
    exp_rem_h2h_wins = exp_rem_h2h_wins
  )
  
  team_summary <- curr_teams %>%
    dplyr::left_join(agg_df,       by = "franchise_id") %>%
    dplyr::left_join(bonus_expect, by = "franchise_id") %>%
    dplyr::mutate(
      exp_rem_ap_wins    = dplyr::coalesce(exp_rem_ap_wins,  0),
      exp_rem_h2h_wins   = dplyr::coalesce(exp_rem_h2h_wins, 0),
      pred_ap_wins       = ap_wins_total + exp_rem_ap_wins,
      pred_h2h_wins      = h2h_wins      + exp_rem_h2h_wins,
      pred_total_bonus   = pred_Q1_bonus + pred_Q2_bonus +
        pred_Q3_bonus + pred_Q4_bonus + pred_RS_bonus,
      exp_rem_bonus_wins = pred_total_bonus - bonus_wins,
      pred_total_wins    = pred_h2h_wins + pred_total_bonus
    )
  
  list(
    team_summary  = team_summary,
    weekly_h2h    = weekly_h2h,
    bonus_expect  = bonus_expect,
    mean_model_m3 = mean_mod_m3
  )
}




########################################################################
#### CREATE PRETTY READOUT GRAPHIC #####################################
########################################################################

build_adl_playoff_graphic <- function(adl_picture, season, week) {
  
  # -------------------------------------------------------------------
  # 0. Make sure we have the columns we need, with sane aliases
  # -------------------------------------------------------------------
  adl_picture <- adl_picture %>%
    dplyr::mutate(
      # Qual flags: prefer 'entry' if present, otherwise 'qual'
      entry     = dplyr::coalesce(.data$entry, .data$qual),
      # Current AP wins: prefer 'ap_wins' alias, else ap_wins_total
      ap_wins   = dplyr::coalesce(.data$ap_wins, .data$ap_wins_total),
      # Projected total wins: prefer 'pred_wins' alias, else pred_total_wins
      pred_wins = dplyr::coalesce(.data$pred_wins, .data$pred_total_wins)
    )
  
  # We assume:
  #   - conference is coded "00" = NFC, "01" = AFC
  #   - seed, franchise_name, total_wins, points_for, potential_points,
  #     pred_ap_wins, pred_finish all exist from your wrapper
  
  # -------------------------------------------------------------------
  # 1. Split into NFC / AFC and select the 10 columns you want
  # -------------------------------------------------------------------
  playoff_cols <- c(
    "entry",
    "seed",
    "franchise_name",
    "total_wins",
    "ap_wins",
    "points_for",
    "potential_points",
    "pred_wins",
    "pred_ap_wins",
    "pred_finish"
  )
  
  nfc_df <- adl_picture %>%
    dplyr::filter(conference == "00") %>%
    dplyr::arrange(seed)
  
  afc_df <- adl_picture %>%
    dplyr::filter(conference == "01") %>%
    dplyr::arrange(seed)
  
  if (nrow(nfc_df) == 0 || nrow(afc_df) == 0) {
    warning(
      "Expected NFC (conference == '00') and AFC (conference == '01') rows.\n",
      "Got: ", nrow(nfc_df), " NFC and ", nrow(afc_df), " AFC."
    )
  }
  
  nfc_tbl <- nfc_df %>%
    dplyr::select(dplyr::all_of(playoff_cols))
  
  afc_tbl <- afc_df %>%
    dplyr::select(dplyr::all_of(playoff_cols))
  
  # -------------------------------------------------------------------
  # 2. Build NFC / AFC gt tables with your labels & rounding
  # -------------------------------------------------------------------
  label_cols <- list(
    entry            = "Qual",
    seed             = "Seed",
    franchise_name   = "Team",
    total_wins       = "Total Wins",
    ap_wins          = "AP Wins",
    points_for       = "Points For",
    potential_points = "Potential Pts",
    pred_wins        = "Pred. Wins",
    pred_ap_wins     = "Pred. AP Wins",
    pred_finish      = "Pred. Finish"
  )
  
  # Helper to apply shared formatting
  format_playoff_table <- function(tbl, conf_label) {
    gt::gt(tbl) %>%
      gt::tab_header(
        title = glue::glue("{conf_label} Playoff Picture (Week {week})")
      ) %>%
      gt::cols_label(.list = label_cols) %>%
      gt::fmt_number(columns = "pred_wins",    decimals = 2) %>%
      gt::fmt_number(columns = "pred_ap_wins", decimals = 1) %>%
      gt::tab_source_note(
        # No "Entry key" text, just the legend
        gt::md("y = Division winner &nbsp;&nbsp;&nbsp;&nbsp; x = Wild Card")
      ) %>%
      # 👉 Restore Qual styling: italic + right-aligned
      gt::cols_align(
        columns = "entry",
        align   = "right"
      ) %>%
      gt::tab_style(
        style = gt::cell_text(style = "italic"),
        locations = gt::cells_body(columns = "entry")
      )
  }
  
  playoff_nfc_gt <- format_playoff_table(nfc_tbl, "NFC")
  playoff_afc_gt <- format_playoff_table(afc_tbl, "AFC")
  
  # -------------------------------------------------------------------
  # 3. Build draft order grid (using current logic, just nicer labels)
  # -------------------------------------------------------------------
  build_conf_draft <- function(df_conf,
                               seed_col,
                               pot_col,
                               seed_playoff_max = 7L,
                               seed_consol_min  = 8L) {
    # Consolation ladder teams (seeds 8–16)
    consol <- df_conf %>%
      dplyr::filter(.data[[seed_col]] >= seed_consol_min) %>%
      dplyr::arrange(.data[[pot_col]]) %>%  # weaker roster (low pot pts) => earlier pick
      dplyr::mutate(Pick = dplyr::row_number()) %>%
      dplyr::select(Pick, Team = franchise_name)
    
    # Playoff teams (seeds 1–7)
    playoff <- df_conf %>%
      dplyr::filter(.data[[seed_col]] <= seed_playoff_max) %>%
      dplyr::arrange(.data[[pot_col]]) %>%
      dplyr::mutate(Pick = dplyr::row_number() + nrow(consol)) %>%
      dplyr::select(Pick, Team = franchise_name)
    
    dplyr::bind_rows(consol, playoff)
  }
  
  # As-of-today draft order (using current seed + potential_points)
  nfc_today <- build_conf_draft(
    df_conf = nfc_df,
    seed_col = "seed",
    pot_col  = "potential_points"
  )
  afc_today <- build_conf_draft(
    df_conf = afc_df,
    seed_col = "seed",
    pot_col  = "potential_points"
  )
  
  # Projected draft order:
  #   - Use pred_finish as the "projected seed"
  #   - Still sort by potential_points as the roster-strength metric
  nfc_pred <- build_conf_draft(
    df_conf = nfc_df %>% dplyr::mutate(pred_seed = pred_finish),
    seed_col = "pred_seed",
    pot_col  = "potential_points"
  )
  afc_pred <- build_conf_draft(
    df_conf = afc_df %>% dplyr::mutate(pred_seed = pred_finish),
    seed_col = "pred_seed",
    pot_col  = "potential_points"
  )
  
  # Combine into a 4-block grid: NFC Today | NFC Proj | AFC Today | AFC Proj
  draft_grid <- nfc_today %>%
    dplyr::rename(
      `NFC (As of Today) Pick` = Pick,
      `NFC (As of Today) Team` = Team
    ) %>%
    dplyr::bind_cols(
      nfc_pred %>%
        dplyr::rename(
          `NFC (Projected) Pick` = Pick,
          `NFC (Projected) Team` = Team
        ),
      afc_today %>%
        dplyr::rename(
          `AFC (As of Today) Pick` = Pick,
          `AFC (As of Today) Team` = Team
        ),
      afc_pred %>%
        dplyr::rename(
          `AFC (Projected) Pick` = Pick,
          `AFC (Projected) Team` = Team
        )
    )
  
  # Build gt table with spanners so each header phrase appears only once
  draft_gt <- draft_grid %>%
    dplyr::rename(
      nfc_today_pick  = `NFC (As of Today) Pick`,
      nfc_today_team  = `NFC (As of Today) Team`,
      nfc_proj_pick   = `NFC (Projected) Pick`,
      nfc_proj_team   = `NFC (Projected) Team`,
      afc_today_pick  = `AFC (As of Today) Pick`,
      afc_today_team  = `AFC (As of Today) Team`,
      afc_proj_pick   = `AFC (Projected) Pick`,
      afc_proj_team   = `AFC (Projected) Team`
    ) %>%
    gt::gt() %>%
    gt::tab_header(
      title = glue::glue("Projected {season + 1} ADL Draft Order")
    ) %>%
    # Blank column labels so "Pick"/"Team" text disappears,
    # but keep the header row so the spanners still show.
    gt::cols_label(
      nfc_today_pick  = "",
      nfc_today_team  = "",
      nfc_proj_pick   = "",
      nfc_proj_team   = "",
      afc_today_pick  = "",
      afc_today_team  = "",
      afc_proj_pick   = "",
      afc_proj_team   = ""
    ) %>%
    gt::tab_spanner(
      label   = "NFC (As of Today)",
      columns = c(nfc_today_pick, nfc_today_team)
    ) %>%
    gt::tab_spanner(
      label   = "NFC (Projected)",
      columns = c(nfc_proj_pick, nfc_proj_team)
    ) %>%
    gt::tab_spanner(
      label   = "AFC (As of Today)",
      columns = c(afc_today_pick, afc_today_team)
    ) %>%
    gt::tab_spanner(
      label   = "AFC (Projected)",
      columns = c(afc_proj_pick, afc_proj_team)
    )
  
  # -------------------------------------------------------------------
  # 4. Return the three gt objects
  # -------------------------------------------------------------------
  list(
    playoff_nfc  = playoff_nfc_gt,
    playoff_afc  = playoff_afc_gt,
    draft_table  = draft_gt
  )
}






####################################################
### DEFINE FINAL WRAPPER FUNCTION #################
####################################################

get_adl_playoff_picture <- function(season,
                                    week,
                                    max_week     = adl_max_week,
                                    n_bonus_sims = 3000L) {
  season <- as.integer(season)
  week   <- as.integer(week)
  
  # -------------------------------------------------
  # 0. Sanity checks / required globals
  # -------------------------------------------------
  if (!exists("ADL_weekly_history_2021_2025")) {
    stop("Object 'ADL_weekly_history_2021_2025' must exist before calling get_adl_playoff_picture().")
  }
  if (!exists("mfl_conns")) {
    stop("Global 'mfl_conns' (from load_mfl_conns()) must exist before calling get_adl_playoff_picture().")
  }
  
  # -------------------------------------------------
  # 1. Current season-to-date standings & live seeds
  # -------------------------------------------------
  standings_raw <- build_adl_weekly_results(season = season, week = week)
  snapshot_curr <- add_adl_playoff_snapshot(standings_raw)
  # snapshot_curr now has:
  #   qual, seed, h2h_wins, bonus_wins, total_wins,
  #   ap_wins_total, points_for, potential_points, conference, division, etc.
  
  # -------------------------------------------------
  # 2. Prep inputs for Monte Carlo: sched + sd_points
  # -------------------------------------------------
  # 2a) Connection + schedule for this season
  season_suffix <- substr(as.character(season), 3, 4)  # 2025 -> "25"
  conn_name     <- paste0("ADL", season_suffix)        # "ADL25"
  
  mfl_conn <- mfl_conns[[conn_name]]
  if (is.null(mfl_conn)) {
    stop("No MFL connection named ", conn_name, " found in load_mfl_conns().")
  }
  
  sched_df <- ffscrapr::ff_schedule(mfl_conn) %>%
    dplyr::select(week, franchise_id, opponent_id)
  
  # 2b) SD of weekly points across history (simple overall average)
  history_df <- ADL_weekly_history_2021_2025
  
  sd_points <- history_df %>%
    dplyr::filter(week <= max_week) %>%
    dplyr::group_by(season, franchise_id) %>%
    dplyr::summarise(
      points_sd = sd(points_for_week, na.rm = TRUE),
      .groups   = "drop"
    ) %>%
    dplyr::summarise(
      overall_sd = mean(points_sd, na.rm = TRUE),
      .groups    = "drop"
    ) %>%
    dplyr::pull(overall_sd)
  
  # -------------------------------------------------
  # 3. Run Monte Carlo (this is where the progress bar appears)
  # -------------------------------------------------
  mc_res <- run_adl_monte_carlo(
    standings_df = snapshot_curr,
    history_df   = history_df,
    sched_df     = sched_df,
    sd_points    = sd_points,
    max_week     = max_week,
    n_sims       = n_bonus_sims
  )
  # mc_res$team_summary has:
  #   franchise_id, ap_wins_total, h2h_wins, total_wins,
  #   pred_ap_wins, pred_h2h_wins, pred_total_bonus, pred_total_wins, etc.
  
  team_pred <- mc_res$team_summary %>%
    dplyr::select(
      franchise_id,
      pred_ap_wins,
      pred_h2h_wins,
      pred_total_bonus,
      pred_total_wins
    )
  
  # -------------------------------------------------
  # 4. Combine live standings with projections
  # -------------------------------------------------
  # Final regular season:
  #   - 12 H2H weeks + 5 bonus events = 17 total games
  n_teams        <- dplyr::n_distinct(snapshot_curr$franchise_id)
  ap_games_total <- (n_teams - 1L) * max_week
  final_games    <- 17L
  
  snapshot_pred <- snapshot_curr %>%
    dplyr::left_join(team_pred, by = "franchise_id") %>%
    dplyr::mutate(
      # If MC fields are missing for whatever reason, fall back to actuals
      pred_ap_wins     = dplyr::coalesce(pred_ap_wins,     ap_wins_total),
      pred_h2h_wins    = dplyr::coalesce(pred_h2h_wins,    h2h_wins),
      pred_total_bonus = dplyr::coalesce(pred_total_bonus, bonus_wins),
      pred_total_wins  = dplyr::coalesce(pred_total_wins,  total_wins),
      
      # Projected win% over 17 total games (12 H2H + 5 bonus events)
      pred_win_pct = pred_total_wins / final_games,
      
      # Projected all-play win%: AP games are the same for everyone,
      # so we just divide by the scalar ap_games_total.
      pred_ap_win_pct = if (ap_games_total > 0) {
        pred_ap_wins / ap_games_total
      } else {
        NA_real_
      }
    )
  
  
  # -------------------------------------------------
  # 5. Projected seeding (division winners + wildcards)
  # -------------------------------------------------
  # 5.1 Division winners (projected)
  pred_div_winners <- snapshot_pred %>%
    dplyr::group_by(conference, division) %>%
    dplyr::arrange(
      dplyr::desc(pred_win_pct),
      dplyr::desc(pred_ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::slice(1) %>%
    dplyr::ungroup() %>%
    dplyr::transmute(
      franchise_id,
      pred_is_division_winner = TRUE
    )
  
  # 5.2 Wild cards (projected): top 3 non-division-winners per conference
  pred_wild_cards <- snapshot_pred %>%
    dplyr::anti_join(pred_div_winners, by = "franchise_id") %>%
    dplyr::group_by(conference) %>%
    dplyr::arrange(
      dplyr::desc(pred_win_pct),
      dplyr::desc(pred_ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::mutate(pred_wc_rank = dplyr::row_number()) %>%
    dplyr::filter(pred_wc_rank <= 3L) %>%
    dplyr::ungroup() %>%
    dplyr::transmute(
      franchise_id,
      pred_is_wild_card = TRUE
    )
  
  # 5.3 Attach projected flags
  snapshot_flagged <- snapshot_pred %>%
    dplyr::left_join(pred_div_winners, by = "franchise_id") %>%
    dplyr::left_join(pred_wild_cards,  by = "franchise_id") %>%
    dplyr::mutate(
      pred_is_division_winner = dplyr::coalesce(pred_is_division_winner, FALSE),
      pred_is_wild_card       = dplyr::coalesce(pred_is_wild_card,       FALSE),
      pred_is_playoff_team    = pred_is_division_winner | pred_is_wild_card
    )
  
  # 5.4 Projected seeds (1–7 playoff, 8–16 consolation)
  pred_playoff <- snapshot_flagged %>%
    dplyr::filter(pred_is_playoff_team) %>%
    dplyr::group_by(conference) %>%
    dplyr::arrange(
      dplyr::desc(pred_ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::mutate(pred_playoff_seed = dplyr::row_number()) %>%
    dplyr::ungroup()
  
  pred_consol <- snapshot_flagged %>%
    dplyr::filter(!pred_is_playoff_team) %>%
    dplyr::group_by(conference) %>%
    dplyr::arrange(
      dplyr::desc(pred_ap_win_pct),
      dplyr::desc(points_for)
    ) %>%
    dplyr::mutate(pred_consol_seed = dplyr::row_number() + 7L) %>%
    dplyr::ungroup()
  
  snapshot_seeded <- dplyr::bind_rows(pred_playoff, pred_consol) %>%
    dplyr::mutate(
      pred_finish = dplyr::if_else(
        pred_is_playoff_team,
        pred_playoff_seed,
        pred_consol_seed
      )
    )
  
  # -------------------------------------------------
  # 6. Attach detailed Monte Carlo outputs for diagnostics
  #    - Per-quarter bonus wins (Q1, Q2, Q3, Q4, RS)
  #    - Per-week H2H wins (W1..W12)
  # -------------------------------------------------
  
  # mc_res$bonus_expect should be one row per franchise_id
  # with predicted bonus wins by segment.
  bonus_expect <- mc_res$bonus_expect
  
  # If bonus_expect uses the older names (pred_Q1_bonus, etc.),
  # rename them to the requested columns. If it already uses the
  # new names, this block will simply be skipped.
  if (all(c("pred_Q1_bonus", "pred_Q2_bonus", "pred_Q3_bonus",
            "pred_Q4_bonus", "pred_RS_bonus") %in% names(bonus_expect))) {
    bonus_expect <- bonus_expect %>%
      dplyr::rename(
        pred_q1_bonus_wins = pred_Q1_bonus,
        pred_q2_bonus_wins = pred_Q2_bonus,
        pred_q3_bonus_wins = pred_Q3_bonus,
        pred_q4_bonus_wins = pred_Q4_bonus,
        pred_rs_bonus_wins = pred_RS_bonus
      )
  }
  
  # mc_res$weekly_h2h should already have columns:
  #   franchise_id, pred_w1_wins, ..., pred_w12_wins
  weekly_h2h <- mc_res$weekly_h2h
  
  # Attach both sets of diagnostics to the seeded snapshot
  snapshot_seeded <- snapshot_seeded %>%
    dplyr::left_join(bonus_expect, by = "franchise_id") %>%
    dplyr::left_join(weekly_h2h,   by = "franchise_id")
  
  # -------------------------------------------------
  # 6a. Data for the GRAPHIC helper (raw / machine names)
  # -------------------------------------------------
  snapshot_for_graphic <- snapshot_seeded %>%
    dplyr::mutate(
      entry     = qual,           # y/x flags for legend
      ap_wins   = ap_wins_total,    # convenience alias
      pred_wins = pred_total_wins   # convenience alias
    )
  
  # -------------------------------------------------
  # 6b. Pretty, human-facing dataframe returned to you
  #      (now WITH the detailed prediction columns)
  # -------------------------------------------------
  snapshot_final <- snapshot_seeded %>%
    dplyr::mutate(
      pred_total_wins = round(pred_total_wins, 2),
      pred_ap_wins    = round(pred_ap_wins,    1)
    ) %>%
    dplyr::rename(
      Qual            = qual,
      Seed            = seed,
      Team            = franchise_name,
      `Total Wins`    = total_wins,
      `AP Wins`       = ap_wins_total,
      `Points For`    = points_for,
      `Potential Pts` = potential_points,
      `Pred. Wins`    = pred_total_wins,
      `Pred. AP Wins` = pred_ap_wins,
      `Pred. Finish`  = pred_finish
    ) %>%
    dplyr::arrange(conference, Seed) %>%
    dplyr::relocate(
      Qual, Seed, Team,
      `Total Wins`, `AP Wins`,
      `Points For`, `Potential Pts`,
      `Pred. Wins`, `Pred. AP Wins`, `Pred. Finish`
    ) %>%
    # Keep conference & division at the end for grouping,
    # all new pred_* columns (weeks/quarters) will sit just before them.
    dplyr::relocate(conference, division, .after = dplyr::last_col())
  
  
  # -------------------------------------------------
  # 7. Build & display pretty HTML graphic
  # -------------------------------------------------
  graphics_list <- build_adl_playoff_graphic(
    adl_picture = snapshot_for_graphic,
    season      = season,
    week        = week
  )
  
  nfc_gt   <- graphics_list$playoff_nfc
  afc_gt   <- graphics_list$playoff_afc
  draft_gt <- graphics_list$draft_table
  
  # --- Output path ---
  out_dir <- "C:/Users/filim/Documents/R/LeagueFeatures/PlayoffPicture"
  if (!dir.exists(out_dir)) dir.create(out_dir, recursive = TRUE)
  
  html_file <- file.path(
    out_dir,
    sprintf("ADL_%d_W%02d_playoff_and_draft.html", season, week)
  )
  
  # --- Build mobile-friendly HTML with "Last updated" line ---
  if (!requireNamespace("htmltools", quietly = TRUE)) {
    warning("Package 'htmltools' not installed; cannot create HTML graphic.")
  } else {
    nfc_html   <- gt::as_raw_html(nfc_gt)
    afc_html   <- gt::as_raw_html(afc_gt)
    draft_html <- gt::as_raw_html(draft_gt)
    
    # Get a timestamp; you can tweak tz/format to taste
    updated_time <- format(
      Sys.time(),
      tz = "America/Toronto",
      usetz = TRUE
    )
    
    page <- htmltools::tagList(
      htmltools::tags$html(
        htmltools::tags<head>(
          htmltools::tags$meta(charset = "utf-8"),
          htmltools::tags$meta(
            name = "viewport",
            content = "width=device-width, initial-scale=1.0"
          ),
          htmltools::tags$title(
            sprintf("ADL %d Week %d Playoff Picture & Draft Preview", season, week)
          ),
          # Minimal responsive styling
          htmltools::tags$style(HTML("
            body {
              font-family: system-ui, -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
              margin: 0;
              padding: 0;
              background-color: #f5f5f5;
            }
            .page-wrapper {
              max-width: 1100px;
              margin: 0 auto;
              padding: 16px;
            }
            .page-title {
              text-align: center;
              font-size: 1.8rem;
              font-weight: 600;
              margin: 12px 0 4px 0;
            }
            .page-subtitle {
              text-align: center;
              font-size: 0.9rem;
              color: #555;
              margin-bottom: 20px;
            }
            .table-wrapper {
              background-color: #ffffff;
              border-radius: 8px;
              padding: 8px;
              margin-bottom: 16px;
              box-shadow: 0 2px 4px rgba(0,0,0,0.06);
              overflow-x: auto; /* Horizontal scroll on small screens */
            }
            hr {
              border: none;
              border-top: 1px solid #ddd;
              margin: 24px 0;
            }
          "))
        ),
        htmltools::tags$body(
          htmltools::div(
            class = "page-wrapper",
            htmltools::div(
              class = "page-title",
              sprintf("ADL %d Week %d Playoff Picture & Draft Preview", season, week)
            ),
            htmltools::div(
              class = "page-subtitle",
              sprintf("Last updated at %s", updated_time)
            ),
            htmltools::div(
              class = "table-wrapper",
              htmltools::HTML(nfc_html)
            ),
            htmltools::div(
              class = "table-wrapper",
              htmltools::HTML(afc_html)
            ),
            htmltools::tags$hr(),
            htmltools::div(
              class = "table-wrapper",
              htmltools::HTML(draft_html)
            )
          )
        )
      )
    )
    
    htmltools::save_html(page, file = html_file)
    
    if (interactive() && file.exists(html_file)) {
      if (requireNamespace("rstudioapi", quietly = TRUE)) {
        rstudioapi::viewer(html_file)
      } else {
        utils::browseURL(html_file)
      }
    }
  }
  
  attr(snapshot_final, "html_file") <- html_file
  
  snapshot_final
}


########################################################################
########### Function to Publish to GitHub ##############################
########################################################################

publish_adl_html_to_github <- function(
    season,
    week,
    repo_dir       = "C:/Users/filim/Documents/R/LeagueFeatures/PlayoffPicture",
    branch         = "main",
    remote         = "origin",
    commit_message = NULL
) {
  season <- as.integer(season)
  week   <- as.integer(week)
  
  # 0. Build the latest HTML via your existing pipeline ----------------
  message("Building ADL playoff picture HTML for season ", season,
          ", week ", week, " ...")
  
  snapshot <- get_adl_playoff_picture(season = season, week = week)
  
  html_file <- attr(snapshot, "html_file")
  if (is.null(html_file) || !file.exists(html_file)) {
    stop("get_adl_playoff_picture() did not produce a valid 'html_file' attribute.")
  }
  
  # 1. Copy (or rename) to index.html at repo root ---------------------
  #    This is what GitHub Pages will serve.
  if (!dir.exists(repo_dir)) {
    stop("Repo directory does not exist: ", repo_dir)
  }
  
  index_path <- file.path(repo_dir, "index.html")
  file.copy(html_file, index_path, overwrite = TRUE)
  
  message("Wrote index.html to: ", index_path)
  
  # 2. Run Git commands inside repo_dir --------------------------------
  old_wd <- getwd()
  on.exit(setwd(old_wd), add = TRUE)
  setwd(repo_dir)
  
  # Helper to run git commands and report non-zero exit codes nicely
  run_git <- function(cmd) {
    full_cmd <- paste("git", cmd)
    status <- system(full_cmd)
    if (status != 0) {
      stop("Git command failed (exit code ", status, "): ", full_cmd)
    }
    invisible(status)
  }
  
  # 2a. Quick sanity check: are we actually in a git repo?
  status <- system("git rev-parse --is-inside-work-tree",
                   ignore.stdout = TRUE, ignore.stderr = TRUE)
  if (status != 0) {
    stop("Directory '", repo_dir, "' is not a Git repository. ",
         "Run 'git init' and 'git remote add ", remote,
         " <your-remote-url>' once before using this function.")
  }
  
  # 2b. Stage the updated index.html
  run_git("add index.html")
  
  # 2c. Only commit if there are changes -------------------------------
  # git diff --cached --quiet returns:
  #   0 if no staged changes
  #   1 if there ARE staged changes
  diff_status <- system("git diff --cached --quiet",
                        ignore.stdout = TRUE, ignore.stderr = TRUE)
  
  if (diff_status == 0) {
    message("No changes to commit (index.html is unchanged). Skipping commit & push.")
    return(invisible(list(snapshot = snapshot, index_path = index_path)))
  }
  
  # 2d. Commit with a nice default message if not supplied
  if (is.null(commit_message)) {
    commit_message <- glue::glue(
      "Update ADL playoff picture: season {season}, week {week} ({Sys.time()})"
    )
  }
  
  run_git(paste("commit -m", shQuote(commit_message)))
  
  # 2e. Push to GitHub
  message("Pushing to GitHub: ", remote, "/", branch, " ...")
  run_git(paste("push", remote, branch))
  
  message("Done! GitHub should pick up the new index.html shortly.")
  
  invisible(list(snapshot = snapshot, index_path = index_path))
}



##########This section is just for making model choices before running function####

## Run below code line if we need to rebuild history df
#ADL_weekly_history_2021_2025 <- build_adl_weekly_history(2021:2025, max_week = adl_max_week)

points_diag <- build_points_params_from_history(
  history_df = ADL_weekly_history_2021_2025,
  max_week   = adl_max_week
)

# 1) Adj.R² table (M1–M5 Points models by week)
view(points_diag$mean_model_comparison)

# 2) Adj.R² plot (M1–M5 Points models)
print(points_diag$mean_model_plot)

# 3) Week 6 Points Model Comparison (M1–M5)
#    One-line: print lm summaries of all 5 Week 6 points models
lapply(points_diag$week6_points_models, summary)

# 4) Week 6 Standard Deviation Model Comparison (S1–S4)
#    One-line: print lm summaries of all 4 Week 6 SD models
lapply(points_diag$week6_sd_models, summary)

# 5) Week-by-week coefficients for Points Model 4 (PF + Pot only)...resist negatives
points_diag$m4_coefs_by_week

# 6) SD-model Adj.R² table (S1–S4 by week)
view(points_diag$sd_model_comparison)

# 7) SD diagnostics (year-by-year average SD + overall average SD)
points_diag$sd_by_season      # year-by-year average SD
points_diag$overall_sd_avg    # overall average SD across seasons



# Build this week's playoff picture + HTML
curr_season <- 2025
weeks_completed   <- 12

adl_playoff_picture <- get_adl_playoff_picture(curr_season, weeks_completed)
view(adl_playoff_picture)

# Auto-publish HTML to GitHub
publish_adl_html_to_github(curr_season, weeks_completed)





