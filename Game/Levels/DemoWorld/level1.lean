import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Game.Metadata

World "DemoWorld"
Level 2

Title "Topology exercise"

Introduction "Topology intro"

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

Statement {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε := by
  Hint "some hint here"
  exact Metric.tendsto_atTop

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl exact

NewTheorem Metric.tendsto_atTop
