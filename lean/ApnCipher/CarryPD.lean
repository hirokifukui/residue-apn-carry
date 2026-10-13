/-
P6-14 (C6, Claude 2026-10-11): ONE component -- the PD layer B = J ∘ F on concrete two-digit
coordinates with carry addition, and its DDT bound in the G directions (u ∉ ker K), for EVERY lift h.
Model: R ≅ F × F (digit 0, digit 1) with addition (a,b) ⊕ (u,v) = (a+u, b+v+c(a,u)); for GR(4,m)
c(a,u) = a ⋆ u (componentwise product in a fixed basis, paper Lemma A of C1 ClassTransition).
The theorem below holds for EVERY function c (no property of c is used), so the identification
c = ⋆ is not an assumption of the Lean statement.
PD layer: B(a,b) = (h(a) + d(a)·b, p(a)); p, h arbitrary; d with d(a+u) = d(a) + k, k ≠ 0
(i.e. d affine with K(u) = k ≠ 0: the G directions of C2 Theorem E, case 1).
The difference relation is B(x ⊕ α) = B(x) ⊕ β, which is equivalent to the ring difference
B(x+α) − B(x) = β in any group.
NOT here: the Z (u = 0) and E (u = ρ) directions, the two-round W2 bound 4/N, the key average
feeding `w2_split_tail_le` (C5 W2Bridge).  Self-contained; no file of c1–c5 is imported.
-/
import Mathlib

noncomputable section

open Finset

namespace ApnCipherC6

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- carry addition on two-digit coordinates. -/
def cadd (c : F → F → F) (x y : F × F) : F × F := (x.1 + y.1, x.2 + y.2 + c x.1 y.1)

/-- the PD layer followed by the digit swap J: B(a,b) = (h a + d a * b, p a). -/
def pdB (p h d : F → F) (x : F × F) : F × F := (h x.1 + d x.1 * x.2, p x.1)

/-- DDT entry for the carry group: #{x : f(x ⊕ α) = f(x) ⊕ β}. -/
def ddtC (c : F → F → F) (f : F × F → F × F) (α β : F × F) : ℕ :=
  (univ.filter (fun x => f (cadd c x α) = cadd c (f x) β)).card

/-- G directions: for each first digit a at most one second digit b solves the difference equation. -/
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

/-- C2 Theorem E, case G, on concrete carry coordinates: DDT ≤ q for every lift h and every β. -/
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

/-- the same bound as a differential probability: DP ≤ 1/q (q = |F|, N = q²). -/
theorem dp_pdB_G_le (c : F → F → F) (p h d : F → F) (α β : F × F) (k : F) (hk : k ≠ 0)
    (hd : ∀ a, d (a + α.1) = d a + k) :
    (ddtC c (pdB p h d) α β : ℝ) / (Fintype.card (F × F) : ℝ) ≤ 1 / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hle : (ddtC c (pdB p h d) α β : ℝ) ≤ Fintype.card F := by
    exact_mod_cast ddtC_pdB_G_le c p h d α β k hk hd
  rw [Fintype.card_prod]
  push_cast
  rw [div_le_div_iff₀ (by positivity) hq]
  calc (ddtC c (pdB p h d) α β : ℝ) * (Fintype.card F : ℝ)
      ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ) := by gcongr
    _ = 1 * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)) := by ring

end ApnCipherC6

end
