import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Logic
import Mathlib.Topology.MetricSpace.PseudoMetric

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

def sequenceLimit (sequence: ℕ → X) (limit: X) :=
  ∀ε:ℝ, ε > 0 → (∃N:ℕ, ∀n:ℕ, n>N → (dist (sequence n) limit) < ε)



lemma max_plus_one_greater_right (a b: ℕ): max a b + 1 > b := calc
  max a b + 1 > max a b := by linarith
  _ ≥ b := by apply le_max_right

lemma max_plus_one_greater_left (a b: ℕ): max a b + 1 > a := calc
  max a b + 1 > max a b := by linarith
  _ ≥ a := by apply le_max_left


lemma uniqueness_of_limit (sequence: ℕ → X) (x₁ x₂: X):
  (sequenceLimit sequence x₁) ∧ (sequenceLimit sequence x₂) → x₁ = x₂ := by
  intro ⟨limit1, limit2⟩
  apply zero_eq_dist.1
  by_contra xs_differ
  rw [← Ne.def] at xs_differ
  symm at xs_differ
  rw [← LE.le.gt_iff_ne dist_nonneg] at xs_differ

  let ε := dist x₁ x₂ / 2
  have ε_pos : ε > 0 := half_pos xs_differ
  specialize limit1 ε ε_pos
  specialize limit2 ε ε_pos
  let ⟨N₁, limit1⟩ := limit1
  let ⟨N₂, limit2⟩ := limit2

  let n := max N₁ N₂ + 1
  specialize limit1 n (max_plus_one_greater_left _ _)
  specialize limit2 n (max_plus_one_greater_right _ _)

  have contrad := calc
    (dist x₁ x₂) ≤ ((dist x₁ (sequence n)) + (dist (sequence n) x₂)) :=
      dist_triangle _ _ _
    _ = ((dist (sequence n) x₁) + (dist (sequence n) x₂)) := by
      rw [dist_comm]
    _ < ε + (dist (sequence n) x₂) :=
      add_lt_add_right limit1 (dist (sequence n) x₂)
    _ < ε + ε := add_lt_add_left limit2 ε
    _ = dist x₁ x₂ := by
      ring

  exact LT.lt.false contrad
