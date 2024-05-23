import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic
import Game.Metadata

World "TopologyWorld"
Level 2

Title "Topology exercise"

Introduction "Topology intro"

open Set

variable {X : Type*} [MetricSpace X]

variable {s t : Set X}

Statement  (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t)  := by
  rw [Metric.isOpen_iff] at *
  Hint "´rintro´ alongside with the anonymous constructor ´⟨ ⟩´ is very useful in destructuring the assumptions"
  rintro x ⟨x_in_s, x_in_t⟩
  rcases hs x x_in_s with ⟨ε₁, ε₁pos, ball_subset_of_s⟩
  rcases ht x x_in_t with ⟨ε₂, ε₂pos, ball_subset_of_t⟩
  use min ε₁ ε₂
  constructor
  · rw [← min_self 0]
    apply min_lt_min ε₁pos ε₂pos
  · intro y y_in_ball
    constructor
    · apply ball_subset_of_s
      apply Metric.ball_subset_ball
      apply min_le_left ε₁ ε₂
      apply y_in_ball
    · apply ball_subset_of_t
      apply Metric.ball_subset_ball
      apply min_le_right ε₁ ε₂
      apply y_in_ball

NewTheorem min_lt_min min_self Metric.ball_subset_ball
