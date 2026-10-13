/-
P8-08 part 1 (C8, Claude 2026-10-12): ONE component -- the class column sums / entries of the
paper's Prop. "table" (sec_3_differential_v3, prop:table) for the PD layer B = J ∘ F, as COUNTS of ddtC
on concrete carry coordinates (F × F, cadd (ApnCipherC7.star e)).  Rows α = (u, v), target β = (s, t):
  Z→Z  (u = 0, v ≠ 0, s = 0)      : entry = 0                               colB_ZZ
  Z→E  (u = 0, s = ρ), all v      : 2 · Σ_v ddtC ≤ q · q   (i.e. ≤ q·(q/2)) colB_ZE   (any ρ ≠ 0)
  E→Z  (u = ρ, s = 0), all v      : Σ_v ddtC ≤ 2q                           colB_EZ
  E→E  (u = ρ, s = ρ), all v      : Σ_v ddtC ≤ 2q   (ρ of weight one)       colB_EE
  G→Z  (u ∉ {0,ρ}, s = 0)         : entry ≤ 2                               entB_GZ
  G→E  (u ∉ {0,ρ}, s = ρ)         : entry ≤ 4       (ρ of weight one)       entB_GE
(divide by N = q² for the paper's normalisation: 0, 1/ω, 2/q, 2/q, 2/N, 2ω/N with ω = 2).
Helpers: memB (= Lemma diffB in carry form), sum_card_filter_le, apn_fiber_le, apn_fiber2_le,
star_single_cases (x ⋆ ρ ∈ {0, ρ} for ρ = e.symm (Pi.single i 1)), card_Q_fiber.
Characteristic 2 is not needed in this file.  Nothing about the specific inverse map.
-/
import ApnCipher.OneRound
-- v3: build of ColsB_v2.lean exit 1 (one remaining coe_filter membership in entB_GZ); fixed, nothing else changed
-- v2: build 1 of ColsB.lean exit 1 (ambiguous `star` vs Star.star; stuck instance in sum_prod_type; set-membership simp); fixed

noncomputable section

open Finset

namespace ApnCipherC8

open ApnCipherC7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- generic counting: Σ_i #{x : P i x} ≤ #T if every solution lies in T and x determines i. -/
theorem sum_card_filter_le {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → α → Prop) [∀ i, DecidablePred (P i)] (T : Finset α)
    (hT : ∀ i x, P i x → x ∈ T) (huniq : ∀ i j x, P i x → P j x → i = j) :
    ∑ i, (univ.filter (P i)).card ≤ T.card := by
  have h1 : ∑ i, (univ.filter (P i)).card
      = (univ.filter (fun z : ι × α => P z.1 z.2)).card := by
    simp only [card_filter]
    exact (Fintype.sum_prod_type (fun z : ι × α => if P z.1 z.2 then (1 : ℕ) else 0)).symm
  rw [h1]
  refine card_le_card_of_injOn Prod.snd ?_ ?_
  · intro z hz
    exact hT _ _ (mem_filter.mp (mem_coe.mp hz)).2
  · intro z hz z' hz' hzz
    have hz1 : P z.1 z.2 := (mem_filter.mp (mem_coe.mp hz)).2
    have hz1' : P z'.1 z'.2 := (mem_filter.mp (mem_coe.mp hz')).2
    have h2 : z.2 = z'.2 := hzz
    have hz2 : P z.1 z'.2 := by rw [← h2]; exact hz1
    exact Prod.ext (huniq _ _ _ hz2 hz1') h2

/-- Lemma diffB in carry form: the two coordinate equations of B(x ⊕ α) = B(x) ⊕ β. -/
theorem memB {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (x α β : F × F) :
    pdB p h d (cadd (ApnCipherC7.star e) x α) = cadd (ApnCipherC7.star e) (pdB p h d x) β ↔
    (h (x.1 + α.1) + d (x.1 + α.1) * (x.2 + α.2 + ApnCipherC7.star e x.1 α.1) = h x.1 + d x.1 * x.2 + β.1 ∧
     p (x.1 + α.1) = p x.1 + β.2 + ApnCipherC7.star e (h x.1 + d x.1 * x.2) β.1) :=
  Prod.ext_iff

/-- APN along u: every fibre of D_u p has at most two points. -/
theorem apn_fiber_le (p : F → F) (u : F)
    (hapn : ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u) (t : F) :
    (univ.filter (fun a => p (a + u) - p a = t)).card ≤ 2 := by
  by_cases hne : (univ.filter (fun a => p (a + u) - p a = t)).Nonempty
  · obtain ⟨a0, ha0⟩ := hne
    rw [mem_filter] at ha0
    have hsub : univ.filter (fun a => p (a + u) - p a = t) ⊆ {a0, a0 + u} := by
      intro a ha
      rw [mem_filter] at ha
      rcases hapn a0 a (by rw [ha0.2, ha.2]) with h0 | h0
      · rw [h0]; exact mem_insert_self _ _
      · rw [h0]; exact mem_insert_of_mem (mem_singleton_self _)
    calc _ ≤ ({a0, a0 + u} : Finset F).card := card_le_card hsub
      _ ≤ 2 := by
        refine (card_insert_le _ _).trans ?_
        simp
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]; omega

/-- two admissible values of D_u p: at most four points. -/
theorem apn_fiber2_le (p : F → F) (u : F)
    (hapn : ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u) (t t' : F) :
    (univ.filter (fun a => p (a + u) - p a = t ∨ p (a + u) - p a = t')).card ≤ 4 := by
  rw [filter_or]
  calc _ ≤ (univ.filter (fun a => p (a + u) - p a = t)).card
          + (univ.filter (fun a => p (a + u) - p a = t')).card := card_union_le _ _
    _ ≤ 2 + 2 := add_le_add (apn_fiber_le p u hapn t) (apn_fiber_le p u hapn t')

/-- weight-one kernel direction: x ⋆ ρ ∈ {0, ρ}. -/
theorem star_single_cases {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (i : Fin m) (y : F) :
    ApnCipherC7.star e y (e.symm (Pi.single i 1)) = 0 ∨
      ApnCipherC7.star e y (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1) := by
  unfold ApnCipherC7.star
  rw [AddEquiv.apply_symm_apply]
  by_cases hy : e y i = 0
  · left
    have : (fun j => e y j * (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j) = 0 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hy]
      · simp [Pi.single_apply, hj]
    rw [this, map_zero]
  · right
    have hy1 := zmod2_eq_one_of_ne_zero _ hy
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hy1]
    · simp [Pi.single_apply, hj]

/-- fibre count of the low output digit Q = h a + d a · b (b ↦ Q bijective, ⋆ s has fibres ≤ q/2). -/
theorem card_Q_fiber {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (A : Finset F) (s : F) (hs : s ≠ 0) (w : F → F) :
    2 * (univ.filter (fun x : F × F => x.1 ∈ A ∧ ApnCipherC7.star e (h x.1 + d x.1 * x.2) s = w x.1)).card
      ≤ A.card * Fintype.card F := by
  set S := univ.filter (fun x : F × F => x.1 ∈ A ∧ ApnCipherC7.star e (h x.1 + d x.1 * x.2) s = w x.1) with hS
  set U := A.biUnion (fun a => (univ.filter (fun y => ApnCipherC7.star e y s = w a)).image (fun y => (a, y)))
    with hU
  have hinj : Set.InjOn (fun x : F × F => (x.1, h x.1 + d x.1 * x.2)) (S : Set (F × F)) := by
    intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    refine Prod.ext h1 ?_
    rw [h1] at h2
    have : d y.1 * x.2 = d y.1 * y.2 := by linear_combination h2
    exact mul_left_cancel₀ (hd0 y.1) this
  have hmaps : Set.MapsTo (fun x : F × F => (x.1, h x.1 + d x.1 * x.2)) (S : Set (F × F))
      (U : Set (F × F)) := by
    intro x hx
    rw [mem_coe] at hx ⊢
    rw [hS, mem_filter] at hx
    rw [hU, mem_biUnion]
    refine ⟨x.1, hx.2.1, ?_⟩
    rw [mem_image]
    exact ⟨h x.1 + d x.1 * x.2, by rw [mem_filter]; exact ⟨mem_univ _, hx.2.2⟩, rfl⟩
  have h1 : S.card ≤ U.card := card_le_card_of_injOn _ hmaps hinj
  have h3 : U.card ≤ ∑ a ∈ A, (univ.filter (fun y => ApnCipherC7.star e y s = w a)).card :=
    card_biUnion_le.trans (sum_le_sum (fun a _ => card_image_le))
  have h4 : 2 * ∑ a ∈ A, (univ.filter (fun y => ApnCipherC7.star e y s = w a)).card
      ≤ A.card * Fintype.card F := by
    rw [mul_sum]
    calc ∑ a ∈ A, 2 * (univ.filter (fun y => ApnCipherC7.star e y s = w a)).card
        ≤ ∑ _a ∈ A, Fintype.card F :=
          sum_le_sum (fun a _ => star_fiber_two_mul_le e s (w a) hs)
      _ = A.card * Fintype.card F := by rw [sum_const, smul_eq_mul]
  exact (Nat.mul_le_mul_left 2 (h1.trans h3)).trans h4

/-! ### The table for B (counts). -/

/-- Z → Z: entry 0 (s = d(a) v ≠ 0). -/
theorem colB_ZZ {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (v : F) (hv : v ≠ 0) (t : F) :
    ddtC (ApnCipherC7.star e) (pdB p h d) ((0 : F), v) ((0 : F), t) = 0 := by
  unfold ddtC
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have hx' := (memB e p h d x _ _).1 hx
  dsimp only at hx'
  obtain ⟨e1, -⟩ := hx'
  simp only [add_zero, star_zero_right] at e1
  have h0 : d x.1 * v = 0 := by linear_combination e1
  exact mul_ne_zero (hd0 _) hv h0

/-- Z → E: column sum over all v of the rows (0, v) into (ρ, t) is ≤ q · (q/2) (any ρ ≠ 0). -/
theorem colB_ZE {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (ρ : F) (hρ : ρ ≠ 0) (t : F) :
    2 * ∑ v, ddtC (ApnCipherC7.star e) (pdB p h d) ((0 : F), v) (ρ, t)
      ≤ Fintype.card F * Fintype.card F := by
  set T := univ.filter (fun x : F × F =>
    x.1 ∈ (univ : Finset F) ∧ ApnCipherC7.star e (h x.1 + d x.1 * x.2) ρ = -t) with hT
  have hTc := card_Q_fiber e h d hd0 univ ρ hρ (fun _ => -t)
  rw [card_univ] at hTc
  have hsum : ∑ v, ddtC (ApnCipherC7.star e) (pdB p h d) ((0 : F), v) (ρ, t) ≤ T.card := by
    unfold ddtC
    refine sum_card_filter_le (fun v x => pdB p h d (cadd (ApnCipherC7.star e) x ((0 : F), v))
      = cadd (ApnCipherC7.star e) (pdB p h d x) (ρ, t)) T ?_ ?_
    · intro v x hx
      have hx' := (memB e p h d x _ _).1 hx
      dsimp only at hx'
      obtain ⟨-, e2⟩ := hx'
      simp only [add_zero] at e2
      rw [hT, mem_filter]
      refine ⟨mem_univ _, mem_univ _, ?_⟩
      linear_combination -e2
    · intro v v' x hx hx'
      have h1 := (memB e p h d x _ _).1 hx
      have h2 := (memB e p h d x _ _).1 hx'
      dsimp only at h1 h2
      obtain ⟨e1, -⟩ := h1
      obtain ⟨e1', -⟩ := h2
      simp only [add_zero, star_zero_right] at e1 e1'
      have : d x.1 * v = d x.1 * v' := by linear_combination e1 - e1'
      exact mul_left_cancel₀ (hd0 x.1) this
  exact (Nat.mul_le_mul_left 2 hsum).trans hTc

/-- E → Z: column sum over v of the rows (ρ, v) into (0, t) is ≤ 2q (APN along ρ). -/
theorem colB_EZ {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (ρ : F) (hapn : ∀ a a', p (a + ρ) - p a = p (a' + ρ) - p a' → a' = a ∨ a' = a + ρ) (t : F) :
    ∑ v, ddtC (ApnCipherC7.star e) (pdB p h d) (ρ, v) ((0 : F), t) ≤ 2 * Fintype.card F := by
  set A := univ.filter (fun a => p (a + ρ) - p a = t) with hA
  have hsum : ∑ v, ddtC (ApnCipherC7.star e) (pdB p h d) (ρ, v) ((0 : F), t) ≤ (A ×ˢ (univ : Finset F)).card := by
    unfold ddtC
    refine sum_card_filter_le (fun v x => pdB p h d (cadd (ApnCipherC7.star e) x (ρ, v))
      = cadd (ApnCipherC7.star e) (pdB p h d x) ((0 : F), t)) _ ?_ ?_
    · intro v x hx
      have hx' := (memB e p h d x _ _).1 hx
      dsimp only at hx'
      obtain ⟨-, e2⟩ := hx'
      simp only [star_zero_right, add_zero] at e2
      rw [mem_product, hA, mem_filter]
      exact ⟨⟨mem_univ _, by linear_combination e2⟩, mem_univ _⟩
    · intro v v' x hx hx'
      have h1 := (memB e p h d x _ _).1 hx
      have h2 := (memB e p h d x _ _).1 hx'
      dsimp only at h1 h2
      obtain ⟨e1, -⟩ := h1
      obtain ⟨e1', -⟩ := h2
      have : d (x.1 + ρ) * v = d (x.1 + ρ) * v' := by linear_combination e1 - e1'
      exact mul_left_cancel₀ (hd0 _) this
  rw [card_product, card_univ] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ (apn_fiber_le p ρ hapn t))

/-- E → E: column sum over v of the rows (ρ, v) into (ρ, t) is ≤ 2q, for ρ of weight one. -/
theorem colB_EE {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (i : Fin m)
    (hapn : ∀ a a', p (a + e.symm (Pi.single i 1)) - p a
      = p (a' + e.symm (Pi.single i 1)) - p a' → a' = a ∨ a' = a + e.symm (Pi.single i 1))
    (t : F) :
    ∑ v, ddtC (ApnCipherC7.star e) (pdB p h d) (e.symm (Pi.single i 1), v) (e.symm (Pi.single i 1), t)
      ≤ 2 * Fintype.card F := by
  have hsc : ∀ y, ApnCipherC7.star e y (e.symm (Pi.single i 1)) = 0 ∨
      ApnCipherC7.star e y (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1) := star_single_cases e i
  have hρ : e.symm (Pi.single i (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have h1 := congrArg e h0
    rw [AddEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 i
    simp at h2
  generalize e.symm (Pi.single i 1) = ρ at hsc hρ hapn ⊢
  set A := univ.filter (fun a => p (a + ρ) - p a = t ∨ p (a + ρ) - p a = t + ρ) with hA
  set T := univ.filter (fun x : F × F => x.1 ∈ A ∧
    ApnCipherC7.star e (h x.1 + d x.1 * x.2) ρ = p (x.1 + ρ) - p x.1 - t) with hT
  have hTc : 2 * T.card ≤ A.card * Fintype.card F :=
    card_Q_fiber e h d hd0 A ρ hρ (fun a => p (a + ρ) - p a - t)
  have hAc : A.card ≤ 4 := apn_fiber2_le p ρ hapn t (t + ρ)
  have hsum : ∑ v, ddtC (ApnCipherC7.star e) (pdB p h d) (ρ, v) (ρ, t) ≤ T.card := by
    unfold ddtC
    refine sum_card_filter_le (fun v x => pdB p h d (cadd (ApnCipherC7.star e) x (ρ, v))
      = cadd (ApnCipherC7.star e) (pdB p h d x) (ρ, t)) T ?_ ?_
    · intro v x hx
      have hx' := (memB e p h d x _ _).1 hx
      dsimp only at hx'
      obtain ⟨-, e2⟩ := hx'
      rw [hT, mem_filter]
      refine ⟨mem_univ _, ?_, ?_⟩
      · rw [hA, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rcases hsc (h x.1 + d x.1 * x.2) with hs | hs
        · left
          rw [hs] at e2
          linear_combination e2
        · right
          rw [hs] at e2
          linear_combination e2
      · linear_combination -e2
    · intro v v' x hx hx'
      have h1 := (memB e p h d x _ _).1 hx
      have h2 := (memB e p h d x _ _).1 hx'
      dsimp only at h1 h2
      obtain ⟨e1, -⟩ := h1
      obtain ⟨e1', -⟩ := h2
      have : d (x.1 + ρ) * v = d (x.1 + ρ) * v' := by linear_combination e1 - e1'
      exact mul_left_cancel₀ (hd0 _) this
  have h8 : 2 * T.card ≤ 4 * Fintype.card F :=
    hTc.trans (Nat.mul_le_mul_right _ hAc)
  omega

/-- G → Z: entry ≤ 2 (b unique per a, APN along u). -/
theorem entB_GZ {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (u v : F) (k : F)
    (hk : k ≠ 0) (hd : ∀ a, d (a + u) = d a + k)
    (hapn : ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u) (t : F) :
    ddtC (ApnCipherC7.star e) (pdB p h d) (u, v) ((0 : F), t) ≤ 2 := by
  unfold ddtC
  set S := univ.filter (fun x => pdB p h d (cadd (ApnCipherC7.star e) x (u, v))
      = cadd (ApnCipherC7.star e) (pdB p h d x) ((0 : F), t)) with hS
  have hinj : Set.InjOn Prod.fst (S : Set (F × F)) := by
    intro x hx y hy hxy
    replace hx := (mem_filter.mp (mem_coe.mp hx)).2
    replace hy := (mem_filter.mp (mem_coe.mp hy)).2
    exact pdB_G_unique (ApnCipherC7.star e) p h d (u, v) ((0 : F), t) k hk hd hx hy hxy
  have hmaps : Set.MapsTo Prod.fst (S : Set (F × F))
      ((univ.filter (fun a => p (a + u) - p a = t) : Finset F) : Set F) := by
    intro x hx
    replace hx := (mem_filter.mp (mem_coe.mp hx)).2
    have hx' := (memB e p h d x _ _).1 hx
    dsimp only at hx'
    obtain ⟨-, e2⟩ := hx'
    simp only [star_zero_right, add_zero] at e2
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, by linear_combination e2⟩
  exact (card_le_card_of_injOn _ hmaps hinj).trans (apn_fiber_le p u hapn t)

/-- G → E: entry ≤ 4 = 2ω for ρ of weight one (b unique per a, D_u p(a) ∈ t ⊕ S_ρ). -/
theorem entB_GE {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (u v : F) (k : F)
    (hk : k ≠ 0) (hd : ∀ a, d (a + u) = d a + k)
    (hapn : ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (i : Fin m) (t : F) :
    ddtC (ApnCipherC7.star e) (pdB p h d) (u, v) (e.symm (Pi.single i 1), t) ≤ 4 := by
  have hsc : ∀ y, ApnCipherC7.star e y (e.symm (Pi.single i 1)) = 0 ∨
      ApnCipherC7.star e y (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1) := star_single_cases e i
  generalize e.symm (Pi.single i 1) = ρ at hsc ⊢
  unfold ddtC
  set S := univ.filter (fun x => pdB p h d (cadd (ApnCipherC7.star e) x (u, v))
      = cadd (ApnCipherC7.star e) (pdB p h d x) (ρ, t)) with hS
  have hinj : Set.InjOn Prod.fst (S : Set (F × F)) := by
    intro x hx y hy hxy
    replace hx := (mem_filter.mp (mem_coe.mp hx)).2
    replace hy := (mem_filter.mp (mem_coe.mp hy)).2
    exact pdB_G_unique (ApnCipherC7.star e) p h d (u, v) (ρ, t) k hk hd hx hy hxy
  have hmaps : Set.MapsTo Prod.fst (S : Set (F × F))
      ((univ.filter (fun a => p (a + u) - p a = t ∨ p (a + u) - p a = t + ρ) : Finset F) :
        Set F) := by
    intro x hx
    replace hx := (mem_filter.mp (mem_coe.mp hx)).2
    have hx' := (memB e p h d x _ _).1 hx
    dsimp only at hx'
    obtain ⟨-, e2⟩ := hx'
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases hsc (h x.1 + d x.1 * x.2) with hs | hs
    · left
      rw [hs] at e2
      linear_combination e2
    · right
      rw [hs] at e2
      linear_combination e2
  exact (card_le_card_of_injOn _ hmaps hinj).trans (apn_fiber2_le p u hapn t (t + ρ))

end ApnCipherC8

end
