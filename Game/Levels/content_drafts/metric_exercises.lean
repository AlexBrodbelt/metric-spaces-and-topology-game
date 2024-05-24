import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Data.Set.Basic

open Set Filter Topology

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  sorry

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

lemma question_1 {X : Type*} [MetricSpace X] : IsOpen { x | dist x c > r } := by
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

lemma question_2 {x : Type*} [TopologicalSpace x] {a : Set x}: interior a = a \ (frontier a) := by
  --  [self_diff_frontier]
  ext x
  constructor
  · intro x_in_interior
    constructor
    · apply interior_subset
      exact x_in_interior
    · by_contra x_in_frontier
      rcases x_in_frontier with ⟨_, x_not_in_interior⟩
      absurd x_not_in_interior x_in_interior
      trivial
  · intro h
    rcases h with ⟨x_in_a, x_not_in_frontier⟩
    rw [frontier, Set.mem_diff, Classical.not_and_iff_or_not_not, not_not_mem] at x_not_in_frontier
    rcases x_not_in_frontier with x_not_in_closure | x_in_interior
    · exact absurd (subset_closure x_in_a) x_not_in_closure
    · exact x_in_interior

lemma question_2_ {x : Type*} [TopologicalSpace x] {a : Set x}: interior a = a \ (frontier a) := by
  rw [self_diff_frontier]

lemma mem_union_ {ι : Type*} {s : ι → Set X} (x_in_union : x ∈ ⋃ i, s i) :  ∃ j, x ∈ s j := by
  apply mem_iUnion.mp x_in_union

lemma topology_closed_under_unions { X ι : Type*} [MetricSpace X]  {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) := by
  rw [Metric.isOpen_iff]
  intro x x_in_union
  rw [mem_iUnion] at x_in_union
  rcases x_in_union with ⟨j, x_in_s_j⟩
  specialize hs j
  rw [Metric.isOpen_iff] at hs
  specialize hs x x_in_s_j
  rcases hs with ⟨ε, εpos, ball_sub⟩
  use ε
  constructor
  · exact εpos
  · intro y y_in_ball
    apply subset_iUnion s j
    apply ball_sub
    apply y_in_ball

lemma topology_closed_under_intersection  {X : Type*} {s t : Set X }[MetricSpace X] (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  rw [Metric.isOpen_iff] at *
  rintro x ⟨x_in_s, x_in_t⟩
  rcases hs x x_in_s with ⟨ε₁, ε₁pos, ball_subset_of_s⟩
  rcases ht x x_in_t with ⟨ε₂, ε₂pos, ball_subset_of_t⟩
  use min ε₁ ε₂
  constructor
  · rw [← min_self 0]
    exact min_lt_min ε₁pos ε₂pos
  · intro y y_in_ball
    constructor
    · apply ball_subset_of_s
      apply Metric.ball_subset_ball
      apply min_le_left ε₁ ε₂
      apply y_in_ball
    · apply ball_subset_of_t
      apply Metric.ball_subset_ball
      apply min_le_right ε₁ ε₂
      apply y_in_ball

lemma topology_closed_under_finite_intersections {X ι : Type* }[MetricSpace X] [Finite ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋂ i, s i) := by
  rw [← Set.biInter_univ] --;rw [Metric.isOpen_iff]
  apply Set.Finite.induction_to_univ (C := λ u ↦ IsOpen (⋂ i ∈ u, s i)) ∅
  · simp_rw [mem_empty_iff_false, iInter_of_empty]
    rw [iInter_univ]
    apply isOpen_univ
    -- [mem_empty_iff_false, , iInter_univ, isOpen_univ]
  · intro S S_neq_univ inter_is_open
    sorry

lemma if_continuous_then_preimage_of_open_is_open {X Y : Type* }[MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : ∀ (x₀ : X), ∀ ε > 0, ∃ δ > 0, ∀ (x : X), dist x x₀ < δ → dist (f x) (f x₀) < ε) {s : Set Y } (hs : IsOpen s) : IsOpen (f ⁻¹' s) := by
  rw [Metric.isOpen_iff] at *
  intro x x_in_preimage
  specialize hs (f x) x_in_preimage
  rcases hs with ⟨ε, εpos, ball_subset_of_s⟩
  specialize hf x ε εpos
  rcases hf with ⟨δ, δpos, h⟩
  use δ
  constructor
  · exact δpos
  · intro y y_in_ball
    apply ball_subset_of_s
    specialize h y y_in_ball
    exact h

-- lemma ball_is_open { X : Type* } [ MetricSpace X ] {x : X} : IsOpen (Metric.ball x ε) := by
--   exact

lemma if_preimage_of_open_is_open_then_continuous  {X Y : Type* }[MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)) : ∀ (x₀ : X), ∀ ε > 0, ∃ δ > 0, ∀ (x : X), dist x x₀ < δ → dist (f x) (f x₀) < ε := by
  intro x ε εpos
  specialize hf (Metric.ball (f x) ε) Metric.isOpen_ball -- proof for Metric.ball is open
  rw [Metric.isOpen_iff] at hf
  -- have : x ∈ f ⁻¹' Metric.ball (f x) ε := by apply (Metric.mem_ball_self εpos)
  specialize hf x (Metric.mem_ball_self εpos)
  rcases hf with ⟨δ, δpos, ball_subset_of_preimage⟩
  use δ
  constructor
  · exact δpos
  · intro x₀ hx₀
    apply ball_subset_of_preimage
    apply hx₀

-- lemma if_closed_then_every_convergent_sequence_converges {X : Type* } [MetricSpace X] {s : Set X} (hs : IsClosed s) : (∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s), ∃ a ∈ X, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (x n) a < ε) → a ∈ s := by sorry

lemma heine_borel_mp {s : Set ℝ} [MetricSpace ℝ ] : IsSeqCompact s → (IsClosed s) ∧ (Bornology.IsBounded s) := by
  intro s_is_sequentially_compact
  constructor
  · sorry
  · sorry

lemma if_compact_then_sequentially_compact {s : Set X} (hs : IsCompact s) : IsSeqCompact s := by
  intro x x_in_s
  rw [isCompact_iff_finite_subcover] at hs
  sorry


example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (eventually_of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

lemma helper {s : Set X} : IsOpen (closure s)ᶜ := by
  apply isOpen_compl_iff.mpr
  apply isClosed_closure


lemma converging_sequence_in_closure_of_s {u : ℕ → X} (s_is_closed : IsClosed s )(hu : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ s := by
  apply closure_subset_iff_isClosed.mpr s_is_closed
  by_contra a_not_in_closure
  rw [← mem_compl_iff] at a_not_in_closure
  have h : IsOpen (closure s)ᶜ := isOpen_compl_iff.mpr isClosed_closure
  rw [Metric.isOpen_iff] at h
  specialize h a a_not_in_closure
  rcases h with ⟨ε, εpos, ball_subset_closure_compl⟩
  specialize hu ε εpos
  rcases hu with ⟨N, u_n_in_εball⟩
  specialize u_n_in_εball N (le_refl N)
  have u_N_not_in_closure : (u N) ∈ (closure s)ᶜ := by apply ball_subset_closure_compl u_n_in_εball
  specialize hs N
  have u_N_in_closure : (u N) ∈ closure s := by apply subset_closure hs
  absurd u_N_not_in_closure u_N_in_closure
  trivial

lemma closed_iff_every_convergent_sequence_converges {s : Set X }: (∀ u : ℕ → s, (∃ a : s, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) a < ε)) → IsClosed s := by
  intro u_converges_in_s
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x x_in_s_compl
  by_contra h
  push_neg at h
  -- rw [Set.not_subset] at h
  let r : ℕ → ℝ := fun n ↦ (1 / (n + 1))
  have rpos : ∀ n : ℕ, r n > 0 := by intro n; simp_rw [one_div, gt_iff_lt, inv_pos]; sorry
  -- let y : ℕ → s := fun n ↦ rcases
  have h₀ : ∀ ε > 0, ∃ y ∈ Metric.ball x ε, y ∈ s := by
    intro ε εpos
    specialize h ε εpos
    rw [Set.not_subset] at h
    rcases h with ⟨y, y_in_s⟩
    rw [not_mem_compl_iff] at y_in_s
    exact ⟨y, y_in_s⟩
  -- let ⟨y : ℕ → s, h₁ : ∀ n, (y n) ∈ Metric.ball x (r n) , h₂ : ∀ n, (y n) ∈ s⟩ := fun n => (h₀ (r n) (rpos n))
  sorry

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩


theorem isClosed_of_closure_subset_ {s : Set X} (h : closure s ⊆ s) : IsClosed s := by
  rw [subset_closure.antisymm h]; exact isClosed_closure

lemma closed_iff_eq_closure {s : Set X} : IsClosed s ↔ s = closure s := by
  constructor
  · intro s_is_closed
    rw [IsClosed.closure_eq s_is_closed]
  · intro s_eq_closure_s
    sorry



example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_forall_le hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_forall_ge hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

#check IsCompact.isClosed

example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f :=
  sorry

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

open BigOperators

open Finset

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry


open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
