import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic
import Game.Metadata

World "TopologyWorld"
Level 4

Title ""

Introduction "Topology intro"

open Set Topology

variable {X Y: Type*} [MetricSpace X] [MetricSpace Y]

variable {f : X → Y}

Statement  (hf : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)) : ∀ (x₀ : X), ∀ ε > 0, ∃ δ > 0, ∀ (x : X), dist x x₀ < δ → dist (f x) (f x₀) < ε := by
  intro x ε εpos
  specialize hf (Metric.ball (f x) ε) Metric.isOpen_ball -- proof for Metric.ball is open
  rw [Metric.isOpen_iff] at hf
  -- have : x ∈ f ⁻¹' Metric.ball (f x) ε := by apply (Metric.mem_ball_self εpos)
  specialize hf x (Metric.mem_ball_self εpos)
  rcases hf with ⟨δ, δpos, ball_subset_of_preimage⟩
  use δ
  constructor
  · exact δpos
  · intro x₀ hx₀
    apply ball_subset_of_preimage
    apply hx₀

NewTheorem Metric.isOpen_ball Metric.mem_ball_self
