import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic
import Game.Metadata

World "TopologyWorld"
Level 3

Title "The preimage of an open set for a given continuous map is again an open set"

Introduction "Topology intro"

open Set Topology

variable {X Y: Type*} [MetricSpace X] [MetricSpace Y]

variable {f : X → Y}

Statement  (hf : ∀ (x₀ : X), ∀ ε > 0, ∃ δ > 0, ∀ (x : X), dist x x₀ < δ → dist (f x) (f x₀) < ε) {s : Set Y } (hs : IsOpen s) : IsOpen (f ⁻¹' s) := by
  rw [Metric.isOpen_iff] at *
  intro x x_in_preimage
  specialize hs (f x) x_in_preimage
  rcases hs with ⟨ε, εpos, ball_subset_of_s⟩
  specialize hf x ε εpos
  rcases hf with ⟨δ, δpos, h⟩
  use δ
  constructor
  · exact δpos
  · intro y y_in_ball
    apply ball_subset_of_s
    specialize h y y_in_ball
    exact h

-- NewTheorem min_lt_min min_self Metric.ball_subset_ball
