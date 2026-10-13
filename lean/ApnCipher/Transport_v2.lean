/-
P7-12 part 3 (C7, Claude 2026-10-12): ONE component -- the entrance to C5 W2Bridge.
C5 W2Bridge states its hypotheses hb1–hb4 for `ddt` / `avgDP` on an abstract finite additive group
(the Galois ring R, difference f(x+a) − f(x) = b).  CarryPD / CarryZ / CarryE / OneRound work on
two-digit carry coordinates F × F with ⊕ = cadd.  Here:
  * `ddt`, `avgDP` are copied VERBATIM from C5 W2Bridge (namespace ApnCipherC5) into ApnCipherC7;
  * ddt_eq_ddtC: for ANY additive group G and ANY bijection φ : G ≃ F × F that carries + to cadd c,
    ddt f a b = ddtC c (φ ∘ f ∘ φ⁻¹) (φ a) (φ b)  (exact transport, no hypothesis on f);
  * ddt_pd_le / avgDP_pd_le: if f is the PD layer in these coordinates (any lift h), then for a ≠ 0
    ddt f a b ≤ q, and every keyed family of such layers has avgDP ≤ 1/q  (= ε(B) ≤ 1/q in the
    exact language of W2Bridge's hypotheses).
The identification of GR(4,m) with (F × F, cadd (star e)) is the paper Lemma A of C1 (ClassTransition);
it enters here only as the hypothesis hφ.  NOT here: the two-round local bound 4/N (paper: C1 Theorem S
recurrence + C3 WarmStart arithmetic), which is what hb1–hb4 actually require.
-/
import ApnCipher.OneRound
-- v2: build 1 of Transport.lean exit 1 (unsolved b + f x ↔ f x + b); add_comm added

noncomputable section

open Finset

namespace ApnCipherC7

section Transport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- (verbatim from C5 W2Bridge) DDT count of a map on a finite additive group. -/
def ddt (f : G → G) (a b : G) : ℕ := (univ.filter (fun x => f (x + a) - f x = b)).card

/-- (verbatim from C5 W2Bridge) key-averaged differential probability of a keyed family. -/
def avgDP {κ : Type*} [Fintype κ] (E : κ → G → G) (α δ : G) : ℝ :=
  (∑ k, (ddt (E k) α δ : ℝ)) / (Fintype.card κ * Fintype.card G)

/-- exact transport of the DDT along a carry-additive bijection. -/
theorem ddt_eq_ddtC (c : F → F → F) (φ : G ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd c (φ x) (φ y)) (f : G → G) (a b : G) :
    ddt f a b = ddtC c (fun z => φ (f (φ.symm z))) (φ a) (φ b) := by
  classical
  have key : ∀ x : G, (f (x + a) - f x = b) ↔
      (φ (f (φ.symm (cadd c (φ x) (φ a)))) = cadd c (φ (f (φ.symm (φ x)))) (φ b)) := by
    intro x
    rw [← hφ x a, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hφ (f x) b,
      φ.injective.eq_iff, sub_eq_iff_eq_add, add_comm b]
  unfold ddt ddtC
  refine Finset.card_nbij' (fun x => φ x) (fun z => φ.symm z) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact (key x).1 hx
  · intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    rw [key (φ.symm z), Equiv.apply_symm_apply]
    exact hz
  · intro x _; simp
  · intro z _; simp

/-- the PD layer, transported to any carry-coordinatised group: DDT ≤ q off the zero row. -/
theorem ddt_pd_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (φ : G ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd (star e) (φ x) (φ y))
    (p h : F → F) (K : F →+ F) (ε ρ : F)
    (hρ : ρ ≠ 0) (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = ρ)) (hε : ∀ a, ε + K a ≠ 0)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (f : G → G) (hf : ∀ z, φ (f (φ.symm z)) = pdB p h (fun a => ε + K a) z)
    (a b : G) (ha : a ≠ 0) :
    ddt f a b ≤ Fintype.card F := by
  have hφ0 : φ 0 = 0 := by
    have h00 := hφ 0 0
    simp only [add_zero, cadd] at h00
    -- φ 0 = (2·(φ 0).1, 2·(φ 0).2 + c) ; use the first coordinate then the second
    have h1 : (φ 0).1 = 0 := by
      have := congrArg Prod.fst h00
      simp only at this
      linear_combination -this
    have h2 : (φ 0).2 = 0 := by
      have := congrArg Prod.snd h00
      simp only [h1, star_zero_right] at this
      linear_combination -this
    exact Prod.ext h1 h2
  have hφa : φ a ≠ 0 := by
    intro h0; apply ha; apply φ.injective; rw [h0, hφ0]
  rw [ddt_eq_ddtC (star e) φ hφ f a b]
  have hfun : (fun z => φ (f (φ.symm z))) = pdB p h (fun a => ε + K a) := funext hf
  rw [hfun]
  exact ddtC_pdB_le e p h K ε ρ hρ hker hε hapn (φ a) hφa (φ b)

/-- every keyed family of transported PD layers (any lifts h_k, any p_k, d_k satisfying PD)
has key-averaged DP ≤ 1/q off the zero row: the one-round ε(B) ≤ 1/q in W2Bridge's language. -/
theorem avgDP_pd_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (φ : G ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd (star e) (φ x) (φ y))
    {κ : Type*} [Fintype κ] [Nonempty κ] (E : κ → G → G)
    (hE : ∀ k a b, a ≠ 0 → ddt (E k) a b ≤ Fintype.card F)
    (a b : G) (ha : a ≠ 0) :
    avgDP E a b ≤ 1 / (Fintype.card F : ℝ) := by
  have hcardG : (Fintype.card G : ℝ) = (Fintype.card F : ℝ) * Fintype.card F := by
    have := Fintype.card_congr φ
    rw [Fintype.card_prod] at this
    exact_mod_cast this
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  unfold avgDP
  rw [div_le_div_iff₀ (by rw [hcardG]; positivity) hq]
  have hsum : (∑ k, (ddt (E k) a b : ℝ)) ≤ ∑ _k : κ, (Fintype.card F : ℝ) :=
    Finset.sum_le_sum (fun k _ => by exact_mod_cast hE k a b ha)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hcardG]
  calc (∑ k, (ddt (E k) a b : ℝ)) * (Fintype.card F : ℝ)
      ≤ (Fintype.card κ * (Fintype.card F : ℝ)) * Fintype.card F := by gcongr
    _ = 1 * (Fintype.card κ * ((Fintype.card F : ℝ) * Fintype.card F)) := by ring

end Transport

end ApnCipherC7

end
