import Game.Metadata
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.InformationTheory.Hamming

World "HammingWorld"

Level 1

Title "Hamming distance"


variable {α ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]
variable {γ : ι → Type*} [∀ i, DecidableEq (γ i)]

open Finset Function

def hammingDist_ (x y : ∀ i, β i) : ℕ :=
  (univ.filter fun i => x i ≠ y i).card

#print prefix String

def stringOne : Vector Char 11 := ⟨"Hello World".data, rfl⟩

def stringTwo : Vector Char 11 :=  ⟨"ByeByeWorld".data, rfl⟩

#eval hammingDist_ stringOne.get stringTwo.get

#check hammingDist

-- lemma nonneg_hammingDist : hammingDist


