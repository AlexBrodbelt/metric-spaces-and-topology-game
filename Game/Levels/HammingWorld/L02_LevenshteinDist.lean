import Std.Data.HashMap
import Mathlib.Data.Vector
import Mathlib.Util.Superscript

/-!
  We define a function computing the Levenshtein distance between two strings.
  We use a HashMap to memoize the recursive computation.
-/

open Std (HashMap)

variable {α : Type} [DecidableEq α] [Hashable α]

def levCache (s₁ s₂ : List α) : StateM (HashMap (List α × List α) Nat) Nat := do
  let cache ← get
  match cache.find? (s₁, s₂) with
  | some res => return res
  | none => match s₁, s₂ with
    | s₁, [] => set (cache.insert (s₁,s₂) s₁.length) *> return s₁.length
    | [], s₂ => set (cache.insert (s₁,s₂) s₂.length) *> return s₂.length
    | h₁::t₁, h₂::t₂ =>
      if h₁ = h₂ then
        let tailDist ← levCache t₁ t₂
        set (cache.insert (h₁::t₁, h₂::t₂) tailDist) *> return tailDist
      else do
        let delDist ← levCache t₁ (h₂::t₂)
        let insDist ← levCache (h₁::t₁) t₂
        let subDist ← levCache t₁ t₂
        let res := 1 + Nat.min (Nat.min delDist insDist) subDist
        set (cache.insert (h₁::t₁, h₂::t₂) res) *> return res

def levDist (s₁ s₂ : List α) : Nat := (levCache s₁ s₂).run' {}

def strLev (s₁ s₂ : String) : Nat := levDist s₁.data s₂.data

#eval strLev "acb" "abc"
#eval strLev "kitten" "sitting"
#eval strLev "Hello world" "Goodbye world"


-- def levDist_ (s₁ s₂ : List α) : 
