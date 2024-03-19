import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Game.Metadata

World "DemoWorld"
Level 3

Title "Topology exercise"

Introduction "Topology intro"

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

Statement :
    IsOpen { x | dist x c > r } := by
  Hint "some hint here"
  rw [Metric.isOpen_iff]
  intro a ainG
  dsimp at ainG
  use (dist a c - r) / 2
  constructor
  · apply half_pos
    linarith
  intro b binB
  dsimp
  rw [Metric.ball] at binB; dsimp at binB
  rw [gt_iff_lt]
  have h₀ : - (dist a c - r) / 2 < - dist b a := by linarith [binB]
  have h₁ : dist a c > r + (dist a c - r) / 2 := by linarith
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
Conclusion "this last message appears if the level is solved."

/- use these commands to add items to the game's inventory. -/

NewTactic rw rfl exact linarith ring apply dsimp intro use

NewTheorem gt_iff_lt Metric.isOpen_iff add_lt_add sub_le_iff_le_add add_comm dist_comm
NewDefinition Metric.Ball


/- documentation for tendsto_atTop -/
TheoremDoc Metric.tendsto_atTop as "tendsto_atTop" in "Metric"
