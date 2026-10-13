/-
P7-12 part 2 (C7, Claude 2026-10-12): ONE component -- assembling the three directions into the
one-round bound ε(B) ≤ 1/q for the PD layer on concrete GR(4,m) carry coordinates.
PD hypotheses (as hypotheses, nothing about the specific inverse map):
  d a = ε + K a with K : F →+ F, ker K = {0, ρ}, ρ ≠ 0, and d a ≠ 0 for all a (i.e. ε ∉ Im K);
  p APN: for u ≠ 0, D_u p(a) = D_u p(a') ⇒ a' ∈ {a, a+u}.  h arbitrary.
The G-direction lemma is copied verbatim from C6 `CarryPD.lean` (namespace ApnCipherC6) into
namespace ApnCipherC7 (`pdB_G_unique`, `ddtC_pdB_G_le`), so this tree does not import c6.
Two-to-one-ness of d is DERIVED from the kernel hypothesis (not assumed).
NOT here: column sums, the two-round W2 bound 4/N, the key average feeding W2Bridge.
-/
import ApnCipher.CarryE_v2

noncomputable section

open Finset

namespace ApnCipherC7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- (verbatim from C6) G directions: for each first digit a at most one second digit b. -/
theorem pdB_G_unique (c : F → F → F) (p h d : F → F) (α β : F × F) (k : F) (hk : k ≠ 0)
    (hd : ∀ a, d (a + α.1) = d a + k) {x y : F × F}
    (hx : pdB p h d (cadd c x α) = cadd c (pdB p h d x) β)
    (hy : pdB p h d (cadd c y α) = cadd c (pdB p h d y) β) (hxy : x.1 = y.1) : x = y := by
  have e1 := congrArg Prod.fst hx
  have e2 := congrArg Prod.fst hy
  simp only [pdB, cadd] at e1 e2
  rw [hd] at e1 e2
  rw [← hxy] at e2
  have hkb : k * x.2 = k * y.2 := by linear_combination e1 - e2
  exact Prod.ext hxy (mul_left_cancel₀ hk hkb)

/-- (verbatim from C6) C2 Theorem E, case G: DDT ≤ q for every lift h and every β. -/
theorem ddtC_pdB_G_le (c : F → F → F) (p h d : F → F) (α β : F × F) (k : F) (hk : k ≠ 0)
    (hd : ∀ a, d (a + α.1) = d a + k) :
    ddtC c (pdB p h d) α β ≤ Fintype.card F := by
  unfold ddtC
  have hinj : Set.InjOn Prod.fst
      ((univ.filter (fun x => pdB p h d (cadd c x α) = cadd c (pdB p h d x) β)) : Set (F × F)) := by
    intro x hx y hy hxy
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    exact pdB_G_unique c p h d α β k hk hd hx hy hxy
  calc (univ.filter (fun x => pdB p h d (cadd c x α) = cadd c (pdB p h d x) β)).card
      = ((univ.filter (fun x => pdB p h d (cadd c x α) = cadd c (pdB p h d x) β)).image Prod.fst).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ (univ : Finset F).card := card_le_card (subset_univ _)
    _ = Fintype.card F := card_univ

/-- d = ε + K with ker K = {0, ρ} is at most two-to-one. -/
lemma affine_two_to_one (K : F →+ F) (ε ρ : F)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = ρ)) (y : F) :
    (univ.filter (fun a => ε + K a = y)).card ≤ 2 := by
  classical
  by_cases hne : (univ.filter (fun a => ε + K a = y)).Nonempty
  · obtain ⟨a0, ha0⟩ := hne
    simp only [mem_filter, mem_univ, true_and] at ha0
    have hsub : univ.filter (fun a => ε + K a = y) ⊆ {a0, a0 + ρ} := by
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      have hK : K (a - a0) = 0 := by
        rw [map_sub]; linear_combination ha - ha0
      rcases (hker _).1 hK with h0 | h0
      · simp [show a = a0 by linear_combination h0]
      · simp [show a = a0 + ρ by linear_combination h0]
    calc _ ≤ ({a0, a0 + ρ} : Finset F).card := card_le_card hsub
      _ ≤ 2 := by
        refine (card_insert_le _ _).trans ?_
        simp
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]; omega

/-- One-round bound on concrete carry coordinates: for every nonzero input difference α and
every output difference β, DDT ≤ q; for every PD layer (p APN, d = ε + K, ker K = {0,ρ},
d nowhere 0) and EVERY lift h. -/
theorem ddtC_pdB_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h : F → F) (K : F →+ F) (ε ρ : F)
    (hρ : ρ ≠ 0) (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = ρ)) (hε : ∀ a, ε + K a ≠ 0)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (α : F × F) (hα : α ≠ 0) (β : F × F) :
    ddtC (star e) (pdB p h (fun a => ε + K a)) α β ≤ Fintype.card F := by
  obtain ⟨u, v⟩ := α
  by_cases hu0 : u = 0
  · subst hu0
    have hv : v ≠ 0 := by
      intro hv; apply hα; simp [hv]
    exact ddtC_pdB_Z_le e p h (fun a => ε + K a) hε
      (affine_two_to_one K ε ρ hker) v hv β
  · by_cases huρ : u = ρ
    · subst huρ
      refine ddtC_pdB_E_le e p h (fun a => ε + K a) u hρ hε ?_ (hapn u hρ) v β
      intro a
      have : K u = 0 := (hker u).2 (Or.inr rfl)
      simp [map_add, this]
    · have hk : K u ≠ 0 := by
        intro h0
        rcases (hker u).1 h0 with h1 | h1
        · exact hu0 h1
        · exact huρ h1
      refine ddtC_pdB_G_le (star e) p h (fun a => ε + K a) (u, v) β (K u) hk ?_
      intro a
      simp only [map_add]
      ring

/-- ε(B) ≤ 1/q as a differential probability (N = q²). -/
theorem dp_pdB_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h : F → F) (K : F →+ F) (ε ρ : F)
    (hρ : ρ ≠ 0) (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = ρ)) (hε : ∀ a, ε + K a ≠ 0)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (α : F × F) (hα : α ≠ 0) (β : F × F) :
    (ddtC (star e) (pdB p h (fun a => ε + K a)) α β : ℝ) / (Fintype.card (F × F) : ℝ)
      ≤ 1 / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hle : (ddtC (star e) (pdB p h (fun a => ε + K a)) α β : ℝ) ≤ Fintype.card F := by
    exact_mod_cast ddtC_pdB_le e p h K ε ρ hρ hker hε hapn α hα β
  rw [Fintype.card_prod]
  push_cast
  rw [div_le_div_iff₀ (by positivity) hq]
  calc (ddtC (star e) (pdB p h (fun a => ε + K a)) α β : ℝ) * (Fintype.card F : ℝ)
      ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ) := by gcongr
    _ = 1 * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)) := by ring

end ApnCipherC7

end
