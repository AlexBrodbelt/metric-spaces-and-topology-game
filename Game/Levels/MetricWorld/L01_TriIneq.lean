import Game.Metadata
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

World "MetricWorld"
Level 1

Title "Triangle inequality"

Introduction "# Transitioning to metric spaces
When proving many theorems about limits in real analysis,
the triangle inequality is the biggest ingredient.
In the theory of metric spaces, we will aim to generalise some of these concepts in real
analysis to things other than the real numbers $\\mathbb{R}$
(such as $\\mathbb{R}^2$ or even geometric shapes...).
When we make the jump to the wider setting, we will assume our space $X$
has an associated function $d \\colon X \\times X \\to \\mathbb{R}_{\\geq0}$ where $d(x,y)$
will represent the 'distance' between
$x, y \\in X$ (in place of how $|x-y|$ is used to measure distances in $\\mathbb{R}$).
To behave like we expect distances should, our distance function $d$ must satisfy 2 conditions
which will be part of the metric space axioms:
- $d(x,y) = 0 \\iff x=y$
- $d(x,y) = d(y,x)$
- $d(x,z) \\leq d(x,y) + d(y,z)$ *(the triangle inequality)*

# Task:
Now, to remind ourself about the power of the triangle inequality, let's show it's equivalent
to the reverse triangle inequality (another tool in real analysis) assuming very little about
what the absolute value of real numbers actually is."

Statement:
    (∀ (x y z : ℝ),  |x - y| + |y - z| ≥ |x - z|) ↔
    (∀ (x y : ℝ), |x - y| ≥ |x| - |y|) := by
  Hint "To prove iff statements, use `constructor` to reduce to proving each direction"
  constructor
  · intro tri_ineq x y
    Hint "With what 'special' values can you use the triangle inequality to prove the claim?"
    specialize tri_ineq x y 0
    rw [sub_zero] at tri_ineq
    rw [sub_zero] at tri_ineq
    linarith
  · intro rev_tri_ineq x y z
    specialize rev_tri_ineq (x-z) (y-z)
    rw [sub_sub_sub_comm] at rev_tri_ineq
    rw [sub_self] at rev_tri_ineq
    rw [sub_zero] at rev_tri_ineq
    linarith
Conclusion "The triangle inequality is a key part of many proofs around limits in Real analysis"

/- use these commands to add items to the game's inventory. -/

NewTactic rw nth_rewrite rfl linarith intro constructor specialize

NewTheorem sub_sub_sub_comm sub_self sub_zero
