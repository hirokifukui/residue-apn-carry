/-
P7-12 part 1 (C7, Claude 2026-10-12): ONE component -- the E direction (u = ρ, the kernel direction
of d: d(a+ρ) = d(a)) of the PD layer B = J ∘ F with the concrete GR(4,m) carry ⋆ (from CarryZ).
Proof idea (paper, C2 Theorem E case E): on the solution set the low output digit y = h a + d a·b
determines the solution. Equal y ⇒ equal D_ρ p(a) (high equation) ⇒ a' ∈ {a, a+ρ} (APN along ρ);
a' = a+ρ is excluded by the low equation, whose two values on the pair differ by d(a)·(ρ⋆ρ) = d(a)·ρ ≠ 0;
then b' = b since d a ≠ 0. Hence DDT ≤ q for every lift h and every β (s = 0 included).
Hypotheses: ρ ≠ 0, d a ≠ 0, d(a+ρ) = d a, and APN of p along ρ (D_ρ p(a) = D_ρ p(a') ⇒ a' ∈ {a,a+ρ}).
Characteristic 2 is derived from the basis e, not assumed.
NOT here: assembling all directions, column sums, W2 / W2Bridge.
-/
import ApnCipher.CarryZ
-- v2: case split fixed (C7 build 1 of CarryE.lean failed: exit 1, rfl-substitution of `a`)

noncomputable section

open Finset

namespace ApnCipherC7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
lemma two_eq_zero_of_basis {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) : (2 : F) = 0 := by
  have h : e ((1 : F) + 1) = 0 := by
    rw [map_add]; funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize e 1 i = z
    fin_cases z <;> rfl
  have : (1 : F) + 1 = 0 := by simpa using congrArg e.symm h
  linear_combination this

omit [Fintype F] [DecidableEq F] in
lemma star_self {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (x : F) : star e x x = x := by
  unfold star
  have : (fun i => e x i * e x i) = e x := by
    funext i
    generalize e x i = z
    fin_cases z <;> rfl
  rw [this, AddEquiv.symm_apply_apply]

/-- C2 Theorem E, case E (u = ρ), on concrete carry coordinates: DDT ≤ q for every lift h,
every v and every output difference β, assuming p is APN along ρ. -/
theorem ddtC_pdB_E_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (ρ : F)
    (hρ : ρ ≠ 0) (hd0 : ∀ a, d a ≠ 0) (hdρ : ∀ a, d (a + ρ) = d a)
    (hapn : ∀ a a', p (a + ρ) - p a = p (a' + ρ) - p a' → a' = a ∨ a' = a + ρ)
    (v : F) (β : F × F) :
    ddtC (star e) (pdB p h d) (ρ, v) β ≤ Fintype.card F := by
  classical
  have h2 : (2 : F) = 0 := two_eq_zero_of_basis e
  have hρρ : ∀ a : F, a + ρ + ρ = a := fun a => by linear_combination ρ * h2
  unfold ddtC
  set S := univ.filter (fun x => pdB p h d (cadd (star e) x (ρ, v))
      = cadd (star e) (pdB p h d x) β) with hS
  have hmem : ∀ x ∈ S,
      h (x.1 + ρ) + d x.1 * (x.2 + v + star e x.1 ρ) = h x.1 + d x.1 * x.2 + β.1 ∧
      p (x.1 + ρ) - p x.1 = β.2 + star e (h x.1 + d x.1 * x.2) β.1 := by
    intro x hx
    simp only [hS, mem_filter, mem_univ, true_and, pdB, cadd] at hx
    have e1 := congrArg Prod.fst hx
    have e2 := congrArg Prod.snd hx
    simp only at e1 e2
    rw [hdρ] at e1
    exact ⟨e1, by linear_combination e2⟩
  have hinj : Set.InjOn (fun x : F × F => h x.1 + d x.1 * x.2) (S : Set (F × F)) := by
    rintro ⟨a, b⟩ hx ⟨a', b'⟩ hx' hy
    simp only at hy
    obtain ⟨e1, e2⟩ := hmem _ hx
    obtain ⟨e1', e2'⟩ := hmem _ hx'
    simp only at e1 e2 e1' e2'
    have hD : p (a + ρ) - p a = p (a' + ρ) - p a' := by rw [e2, e2', hy]
    rcases hapn a a' hD with h' | h'
    · -- same first digit: cancel d a
      have hb : d a * b = d a * b' := by rw [h'] at hy; linear_combination hy
      rw [h', mul_left_cancel₀ (hd0 a) hb]
    · -- a' = a + ρ is impossible
      subst h'
      exfalso
      rw [hρρ, hdρ, star_add_left, star_self] at e1'
      have hz : d a * ρ = 0 := by
        linear_combination e1' + e1 - (d a * v + d a * star e a ρ - β.1) * h2
      exact mul_ne_zero (hd0 a) hρ hz
  calc S.card = (S.image (fun x : F × F => h x.1 + d x.1 * x.2)).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ (univ : Finset F).card := card_le_card (subset_univ _)
    _ = Fintype.card F := card_univ

end ApnCipherC7

end
