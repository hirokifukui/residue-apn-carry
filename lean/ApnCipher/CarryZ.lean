/-
P7-11 (C7, Claude 2026-10-12): ONE component -- the Z direction (u = 0, v ≠ 0) of the PD layer
B = J ∘ F on two-digit coordinates, with the CONCRETE GR(4,m) carry c(a,u) = a ⋆ u
(componentwise product in a fixed F₂-basis e : F ≃+ (Fin m → ZMod 2)).
Definitions `cadd`, `pdB`, `ddtC` are copied verbatim from C6 `CarryPD.lean` (namespace ApnCipherC6),
re-declared here in namespace ApnCipherC7 so that this file is self-contained.
Used properties of the concrete carry (proved here, not assumed):
  * star a 0 = 0                        (no carry from a zero low digit),
  * for s ≠ 0 every fibre {x : x ⋆ s = w} has at most |F|/2 points (translation by a basis vector
    in the support of s moves the fibre off itself).
Assumptions on d (the PD hypothesis, stated as hypotheses): d a ≠ 0 and every value of d has at most
two preimages (d two-to-one onto a hyperplane not containing 0). p and h are arbitrary.
NOT here: the E direction (u = ρ), the exact fibre size |F|/2^wt(s), column sums, W2 / W2Bridge.
-/
import Mathlib

noncomputable section

open Finset

namespace ApnCipherC7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- carry addition on two-digit coordinates (verbatim from C6). -/
def cadd (c : F → F → F) (x y : F × F) : F × F := (x.1 + y.1, x.2 + y.2 + c x.1 y.1)

/-- the PD layer followed by the digit swap J (verbatim from C6). -/
def pdB (p h d : F → F) (x : F × F) : F × F := (h x.1 + d x.1 * x.2, p x.1)

/-- DDT entry for the carry group (verbatim from C6). -/
def ddtC (c : F → F → F) (f : F × F → F × F) (α β : F × F) : ℕ :=
  (univ.filter (fun x => f (cadd c x α) = cadd c (f x) β)).card

/-- the concrete GR(4,m) carry: componentwise product in a fixed F₂-basis. -/
def star {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (x y : F) : F :=
  e.symm (fun i => e x i * e y i)

lemma star_zero_right {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (x : F) : star e x 0 = 0 := by
  unfold star
  have : (fun i => e x i * e (0 : F) i) = (0 : Fin m → ZMod 2) := by
    funext i; simp
  rw [this, map_zero]

lemma star_add_left {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (x y s : F) :
    star e (x + y) s = star e x s + star e y s := by
  unfold star
  rw [← map_add]
  congr 1
  funext i
  simp [map_add, add_mul]

lemma zmod2_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl hz
  · rfl

/-- fibres of x ↦ x ⋆ s for s ≠ 0 have at most |F|/2 points. -/
theorem star_fiber_two_mul_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (s w : F) (hs : s ≠ 0) :
    2 * (univ.filter (fun x => star e x s = w)).card ≤ Fintype.card F := by
  classical
  have hes : e s ≠ 0 := by
    intro h; apply hs; simpa using congrArg e.symm h
  obtain ⟨i, hi⟩ : ∃ i, e s i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hes (funext hcon)
  set δ : F := e.symm (Pi.single i 1) with hδ
  have hstarδ : star e δ s = δ := by
    unfold star
    rw [hδ, AddEquiv.apply_symm_apply]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [zmod2_eq_one_of_ne_zero _ hi]
    · simp [Pi.single_apply, hj]
  have hδne : δ ≠ 0 := by
    intro h0
    have : (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) = 0 := by
      have := congrArg e h0
      simpa [hδ] using this
    have h1 := congrFun this i
    simp at h1
  set T := univ.filter (fun x => star e x s = w) with hT
  have hdisj : Disjoint T (T.image (fun x => x + δ)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    simp only [hT, mem_filter, mem_univ, true_and] at hx hy
    rw [star_add_left, hstarδ, hy] at hx
    exact hδne (by simpa using hx)
  have hcard : (T.image (fun x => x + δ)).card = T.card :=
    card_image_of_injective _ (add_left_injective δ)
  have hle : (T ∪ T.image (fun x => x + δ)).card ≤ Fintype.card F := by
    rw [← card_univ]; exact card_le_card (subset_univ _)
  rw [card_union_of_disjoint hdisj, hcard] at hle
  omega

/-- C2 Theorem E, case Z (u = 0, v ≠ 0), on concrete carry coordinates:
DDT ≤ q for every lift h, every p, every output difference β. -/
theorem ddtC_pdB_Z_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F)
    (hd0 : ∀ a, d a ≠ 0) (hd2 : ∀ y, (univ.filter (fun a => d a = y)).card ≤ 2)
    (v : F) (hv : v ≠ 0) (β : F × F) :
    ddtC (star e) (pdB p h d) ((0 : F), v) β ≤ Fintype.card F := by
  classical
  unfold ddtC
  set S := univ.filter (fun x => pdB p h d (cadd (star e) x ((0 : F), v))
      = cadd (star e) (pdB p h d x) β) with hS
  -- membership in S, unfolded
  have hmem : ∀ x ∈ S, d x.1 * v = β.1 ∧ star e (h x.1 + d x.1 * x.2) β.1 = -β.2 := by
    intro x hx
    simp only [hS, mem_filter, mem_univ, true_and, pdB, cadd, add_zero, star_zero_right] at hx
    have e1 := congrArg Prod.fst hx
    have e2 := congrArg Prod.snd hx
    simp only at e1 e2
    constructor
    · linear_combination e1
    · linear_combination -e2
  by_cases hs : β.1 = 0
  · -- no solutions: d a * v = 0 is impossible
    have : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have := (hmem x hx).1
      rw [hs] at this
      exact (mul_ne_zero (hd0 x.1) hv) this
    rw [this, card_empty]; exact Nat.zero_le _
  · set A := univ.filter (fun a => d a = β.1 / v) with hA
    set T := univ.filter (fun y => star e y β.1 = -β.2) with hT
    have hinj : Set.InjOn (fun x : F × F => (x.1, h x.1 + d x.1 * x.2)) (S : Set (F × F)) := by
      intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      refine Prod.ext h1 ?_
      rw [h1] at h2
      have : d y.1 * x.2 = d y.1 * y.2 := by linear_combination h2
      exact mul_left_cancel₀ (hd0 y.1) this
    have hmaps : Set.MapsTo (fun x : F × F => (x.1, h x.1 + d x.1 * x.2)) (S : Set (F × F))
        ((A ×ˢ T : Finset (F × F)) : Set (F × F)) := by
      intro x hx
      obtain ⟨h1, h2⟩ := hmem x hx
      simp only [coe_product, Set.mem_prod, mem_coe, hA, hT, mem_filter, mem_univ, true_and]
      refine ⟨?_, h2⟩
      field_simp
      exact h1
    have h1 : S.card ≤ (A ×ˢ T).card := card_le_card_of_injOn _ hmaps hinj
    rw [card_product] at h1
    have h2 : A.card ≤ 2 := hd2 _
    have h3 : 2 * T.card ≤ Fintype.card F := star_fiber_two_mul_le e β.1 (-β.2) hs
    calc S.card ≤ A.card * T.card := h1
      _ ≤ 2 * T.card := Nat.mul_le_mul_right _ h2
      _ ≤ Fintype.card F := h3

end ApnCipherC7

end
