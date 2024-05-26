
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic
import Game.Metadata

World "TopologyWorld"
Level 5

Title "Converging sequence converges to element in the closure of the set"

Introduction "Topology intro"

open Set

variable {X Y: Type*} [MetricSpace X] [MetricSpace Y]

variable {f : X → Y}

Statement  {s : Set X} {u : ℕ → X} {a : X} (s_is_closed : IsClosed s )(hu : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε) (hs : ∀ n, u n ∈ s) : a ∈ s := by
  apply closure_subset_iff_isClosed.mpr s_is_closed
  by_contra a_not_in_closure
  rw [← mem_compl_iff] at a_not_in_closure
  have h : IsOpen (closure s)ᶜ := isOpen_compl_iff.mpr isClosed_closure
  rw [Metric.isOpen_iff] at h
  specialize h a a_not_in_closure
  rcases h with ⟨ε, εpos, ball_subset_closure_compl⟩
  specialize hu ε εpos
  rcases hu with ⟨N, u_n_in_εball⟩
  specialize u_n_in_εball N (le_refl N)
  have u_N_not_in_closure : (u N) ∈ (closure s)ᶜ := by apply ball_subset_closure_compl u_n_in_εball
  specialize hs N
  have u_N_in_closure : (u N) ∈ closure s := by apply subset_closure hs
  absurd u_N_not_in_closure u_N_in_closure
  trivial

-- NewTheorem min_lt_min min_self Metric.ball_subset_ball
