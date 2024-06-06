import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic
import Game.Metadata

World "MetricWorld"
Level 4

Title "Topology exercise"

Introduction "Topology intro"

open Set Topology Filter


variable {X : Type*} [MetricSpace X] (A B C : X)


Statement {A : Set X} :  interior A = A \ (frontier A) := by
  Hint "To prove to sets are equal we use the axiom of extensionality `ext`, two sets $A$ and $B$ are equal if and only they have the same members"
  ext x
  Hint "To prove iff statements, use `constructor` to reduce to proving each direction"
  constructor
  Hint "Introduce the assumption into the local context by `intro`"
  · intro x_in_interior
    constructor
    · apply interior_subset
      exact x_in_interior
    Hint "To prove by contradiction we use the tactic `by_contra h` where `h` takes the goal as a new assumption."
    · by_contra x_in_frontier
      rcases x_in_frontier with ⟨_, x_not_in_interior⟩
      Hint "When we have to contradicting hypotheses we can use `absurd`"
      absurd x_not_in_interior x_in_interior
      trivial
  · intro x_in_A_minus_boundary
    Hint "Because a ∖ b = a ∩ bᶜ, if x ∈ a ∖ b then x ∈ a ∩ bᶜ. By definition, if x ∈ s ∩ t then x ∈ s and x ∈ t.
          either use `rcases x_in_s_inter_t with ⟨x_in_s, x_in_t⟩` to split the "
    rcases x_in_A_minus_boundary with ⟨x_in_a, x_not_in_frontier⟩
    rw [frontier] at x_not_in_frontier
    Hint "Set difference is implicitly an intersection:  x ∈ a  b ↔ x ∈ a  and x ∈ bᶜ"
    rw [Set.mem_diff] at x_not_in_frontier
    Hint "One of De Morgan's Laws states ¬ (A ∧ B) ↔ (¬ A) ∨ (¬ B)... This might get you somewhere (´not_and_or` is the name this law has in Mathlib)"
    rw [not_and_or, not_not_mem] at x_not_in_frontier
    Hint "one can split an ∨ with `rcases` to create two hopefully easier subgoals"
    rcases x_not_in_frontier with x_not_in_closure | x_in_interior
    Hint "`absurd` proves a goal given ´p´ and ´¬ p´ (in that order) "
    · exact absurd (subset_closure x_in_a) x_not_in_closure
    · exact x_in_interior
Conclusion "This theorem can be found in Mathlib as `self_diff_frontier`"

/- use these commands to add items to the game's inventory. -/

NewTactic rw rfl exact linarith ring apply dsimp intro use rcases by_contra absurd trivial constructor

NewTheorem Set.mem_diff not_and_or Set.not_not_mem interior_subset
NewDefinition Metric.Ball


/- documentation for tendsto_atTop -/
TheoremDoc Metric.tendsto_atTop as "tendsto_atTop" in "Metric"
