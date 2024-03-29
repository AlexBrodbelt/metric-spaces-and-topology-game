import Game.Metadata
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic

World "HammingWorld"
Level 1

Title "Hamming distance"


variable {α ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]
variable {γ : ι → Type*} [∀ i, DecidableEq (γ i)]

open Finset Function

def hammingDist (x y : ∀ i, β i) : ℕ :=
  (univ.filter fun i => x i ≠ y i).card
