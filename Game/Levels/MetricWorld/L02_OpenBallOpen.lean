import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Game.Metadata

World "MetricWorld"
Level 2

Title "Proving the closed ball is closed"

Introduction "# Transitioning to metric spaces
An important property of a set in a metric space is openness, admittedly it is not obvious why this is an interesting property to study
but eventually it will be closely related to convergence of sequences, continuity, sequential compactness, compactness and so forth.

# Task:

Your task is to prove that the closed ball is closed.
To show $S$ is open, we must show that for an arbitrary element $ y \\in S,
there exists a radius $r(y)$ depending (or not) on $y$ such that
$B(y, r(y)) \\subseteq S$"

open Set Filter Topology

variable {X : Type*} [MetricSpace X] (a b c : X)

Statement :
    IsOpen (Metric.ball c r) := by
  Hint "A set $S$ is open if and only if $\\forall x \\in S, \\exists \\varepsilon > 0$ such that $B(x, \\varepsilon) \\subseteq S$. Take a look at `Metric.isOpen_iff` to see how Lean parses this statement"
  rw [Metric.isOpen_iff]
  Hint "Given the goal is to prove a `∀ x ∈ Metric.ball c r, ...` we introduce two variables `x` and `hx` (you can give them other names if you like, but for the sake of future you may want to use these names I have chosen), to be $x$ and the hypothesis on $x$, namely, $x \\in B(c,r)$"
  intros x hx
  Hint "Let's unpack what it means for `x ∈ Metric.ball c r` by using `rw [Metric.mem_ball] at hx`"
  rw [Metric.mem_ball] at hx
  Hint "What choice of ε can you provide such that `ball x ε ⊆ S`? There are many possible choices, but if you are confident try your pick, otherwise I suggest using '(r - dist x c) / 2'"
  use (r - dist x c) / 2
  -- TODO other choices work, which wouldn't trigger the hints,
  -- maybe hint for this specific value
  constructor
  -- · apply half_pos;
  linarith
  Hint "Now we have to prove that if y ∈ ball x ε then y ∈ ball c r"
  -- TODO the user would have used "intro" before, but not in the
  -- context of showing something is a subset
  -- explicit hint here too mb
  intros y hy
  Hint "We unfold the definition of b ∈ ball by `rw [Metric.mem_ball]`"
  rw [Metric.mem_ball]
  rw [Metric.mem_ball] at hy
  calc dist y c
  _ ≤ dist y x + dist x c := by apply dist_triangle
  _ < (r - dist x c) / 2 + dist x c  := by apply add_lt_add_right hy
  _ = (r + dist x c) / 2 := by linarith
  _ < r := by linarith--nth_rewrite 2 [← add_halves r, add_div' r (dist x c) 2]; apply add_lt_add_left hx

Conclusion "You have proved the open ball centred at $c$ with radius $r$ is open! Well done!"

/- use these commands to add items to the game's inventory. -/

NewTactic rw rfl exact linarith ring apply dsimp intro use

NewTheorem gt_iff_lt Metric.isOpen_iff add_lt_add sub_le_iff_le_add add_comm dist_comm
NewDefinition Metric.Ball dist_triangle
