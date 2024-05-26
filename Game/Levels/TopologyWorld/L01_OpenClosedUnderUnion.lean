import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic
import Game.Metadata

World "TopologyWorld"
Level 1

Title "Topology of a metric space is closed under arbitrary union of elements in the topology - the arbitrary union of open sets is itself an open set"

Introduction "Topology intro"

open Set

variable {ι X : Type*} [MetricSpace X]

variable {s : ι → Set X}

Statement (hs : ∀ i, IsOpen (s i))  : IsOpen (⋃ i, s i) := by
  rw [Metric.isOpen_iff]
  intro x x_in_union
  Hint "if $x$ belongs to the union then it must lie in one of the sets $s j$ for some j ∈ ι"
  rw [mem_iUnion] at x_in_union
  Hint "use ´rcases´ to instantiate the set $s j$ to which $x$ belongs to"
  rcases x_in_union with ⟨j, x_in_s_j⟩
  specialize hs j
  rw [Metric.isOpen_iff] at hs
  specialize hs x x_in_s_j
  rcases hs with ⟨ε, εpos, ball_subset_of_s_j⟩
  use ε
  constructor
  · apply εpos
  Hint "We need to prove Metric.ball x ε ⊆ s j ⊆ ⋃ i, s i - Can you do this ?"
  · intro y y_in_ball
    Hint "We go 'backwards' s j ⊆ ⋃ i, s i  - by using ´ apply subset_iUnion s j´. Observe we give ´s´ and ´j´ as parameters for the theorem"
    apply subset_iUnion s j
    apply ball_subset_of_s_j
    apply y_in_ball


NewTheorem Set.subset_iUnion
