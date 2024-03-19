import Game.Metadata
import Mathlib.Tactic
import Mathlib.Data.Real.Basic


--import Mathlib.Util.Delaborators

World "DemoWorld"
Level 1

Title "Triangle inequality"

Introduction "Topology intro"

#check abs (-3)
#check |-3|
#eval abs (-3)
#eval |-3|
#check sub_zero
#check ring_nf

Statement:
    (∀ (x y z : ℝ),  |x - y| + |y - z| ≥ |x - z|) ↔
    (∀ (x y z : ℝ), |(x-z) - (y-z)| ≥ |x-z| - |y-z|) := by
  Hint "To prove iff statements, use `constructor` to reduce to proving each direction"
  constructor
  · intro tri_ineq x y z
    specialize tri_ineq (x-z) (y-z) 0
    rw [sub_zero] at tri_ineq
    rw [sub_zero] at tri_ineq
    linarith
  · intro rev_tri_ineq x y z
    specialize rev_tri_ineq (x-z) (y-z) 0
    rw [sub_zero] at rev_tri_ineq
    rw [sub_zero] at rev_tri_ineq
    sorry
Conclusion "The triangle inequality is a key part of many proofs around limits in Real analysis"

/- use these commands to add items to the game's inventory. -/

NewTactic rw rfl exact linarith ring apply dsimp intro use

NewTheorem gt_iff_lt add_lt_add sub_le_iff_le_add add_comm dist_comm
