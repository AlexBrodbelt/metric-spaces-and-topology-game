import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Game.Metadata

World "MetricWorld"
Level 3

Title "Proving the closed ball is closed"

Introduction "# Transitioning to metric spaces
An important property of a set in a metric space is openness, admittedly it is not obvious why this is an interesting property to study
but eventually it will be closely related to convergence of sequences, continuity, sequential compactness, compactness and so forth.

# Task:

Your task is to prove that the closed ball is closed.
To show $S$ is open, we must show that for an arbitrary element $ y \\in S,
there exists a radius $r(y)$ depending (or not) on $y$ such that
$B(y, r(y)) \\subseteq S$"

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

Statement :
    IsClosed { x | dist x c ≤ r } := by
  Hint "A set $S$ is closed iff $S^c$ is open"
  rw [isOpen_compl_iff.symm, Set.compl_setOf]; simp only [not_le]
  Hint "A set $S$ is open iff ∀ a ∈ S ∃ ε > 0 such that Ball a ε ⊆ S"
  rw [Metric.isOpen_iff]
  intro a ainS
  Hint "try `dsimp at h` to definitionally simplify the hypothesis which states a is in S, it looks a bit unwieldy otherwise..."
  dsimp at ainS
  Hint "what choice of ε can you provide such that ball a ε ⊆ S ? There are many possible choices, but if you are confident try your pick, otherwise I suggest using '(dist a c - r) / 2'"
  use (dist a c - r) / 2
  -- TODO other choices work, which wouldn't trigger the hints,
  -- maybe hint for this specific value
  constructor
  -- · apply half_pos;
  linarith
  Hint "Now we have to prove that if b ∈ ball a ε then b ∈ S"
  -- TODO the user would have used "intro" before, but not in the
  -- context of showing something is a subset
  -- explicit hint here too mb
  intros b binB; dsimp
  Hint "unfold the definition of b ∈ ball"
  rw [Metric.ball] at binB; dsimp at binB
  have h₀ : - (dist a c - r) / 2 < - dist b a := by linarith [binB]
  have h₁ : dist a c > r + (dist a c - r) / 2 := by linarith
  -- REVISIT TODO I'm not sure calc is possible in lean games,
  -- I'll get confirmation on this
  calc
    r = (r + (dist a c - r) / 2)  + -(dist a c - r) / 2 := by ring
    _ < dist a c + - dist b a := by
      apply add_lt_add
      apply h₁
      apply h₀
    _ = dist a c - dist b a := by ring
    _ ≤ dist b c := by
      rw [sub_le_iff_le_add, add_comm, dist_comm b a]
      apply dist_triangle a b c
Conclusion "You have proved S is open! Well done!"

/- use these commands to add items to the game's inventory. -/

NewTactic rw rfl exact linarith ring apply dsimp intro use

NewTheorem gt_iff_lt Metric.isOpen_iff add_lt_add sub_le_iff_le_add add_comm dist_comm
NewDefinition Metric.Ball dist_triangle


/- documentation for tendsto_atTop -/
TheoremDoc Metric.tendsto_atTop as "tendsto_atTop" in "Metric"
