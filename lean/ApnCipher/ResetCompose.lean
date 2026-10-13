/-
P4-14 (C4, Claude 2026-10-11): one component -- the reset post-composition as an EXACT identity of key-averaged
real DDT counts, and its two-fold use for the four-layer split-tail layout (local lengths (2,2,1,1)).
Self-contained (the needed C3 definitions `ddt`, `ddt_col`, `reset_count` are re-proved here verbatim in a new
namespace, so the C3 tree is not touched and no second module has to be built).

  comp E M C L x = C (M (E x) + L)                                     (M : additive automorphism = the mixer)
  sum_reset_ddt : Σ_L ddt (comp E M C L) α γ = Σ_δ ddt E α δ * ddt C (M δ) γ          (exact, any maps E, C)
  avgDP E α δ   = (Σ_k ddt (E k) α δ) / (|κ| |G|)                    (key-averaged differential probability)
  compK E M C   = the keyed composite, key (k, c, L) ∈ κ × κc × G, L the uniform reset
  suffix_avg_le : (∀ δ, avgDP E α δ ≤ b) → ∀ γ, avgDP (compK E M C) α γ ≤ b      (C c permutations)
  four_layer_le : the same twice: E_SB → (M2, L2, S1^(3)) → (M3, L3, S1^(4)).
The hypothesis on E (for the split tail: E = E_SB with the paper bound (4/N)^w from W2 + D1) is an INPUT;
the conclusion for the composite is proved from real counts, not assumed.  Not formalized: E_SB's own bound
(concrete GR(4,m), SHyp/FHyp, general-w D1), and the identification of keyed families with the reference code.
-/
import Mathlib

noncomputable section

namespace ApnCipherC4

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- DDT count of a map on a finite additive group (same definition as C3). -/
def ddt (f : G → G) (a b : G) : ℕ := (univ.filter (fun x => f (x + a) - f x = b)).card

theorem ddt_col (f : G ≃ G) (b : G) : ∑ a, ddt f a b = Fintype.card G := by
  unfold ddt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ x : G, (∑ a : G, if f (x + a) - f x = b then (1 : ℕ) else 0) = 1 := by
    intro x
    have h : ∀ a : G, (f (x + a) - f x = b) ↔ a = f.symm (f x + b) - x := by
      intro a
      constructor
      · intro h
        have h1 : f (x + a) = f x + b := by rw [← h]; abel
        have h2 : x + a = f.symm (f x + b) := by rw [← h1]; simp
        rw [← h2]; abel
      · rintro rfl
        have : x + (f.symm (f x + b) - x) = f.symm (f x + b) := by abel
        rw [this]; simp
    simp_rw [h]
    simp
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  simp

theorem reset_count (C : G → G) (y y' γ : G) :
    (univ.filter (fun L => C (y' + L) - C (y + L) = γ)).card = ddt C (y' - y) γ := by
  unfold ddt
  simp only [Finset.card_filter]
  have e := Equiv.sum_comp (Equiv.addLeft y) (fun x => if C (x + (y' - y)) - C x = γ then (1 : ℕ) else 0)
  rw [← e]
  refine Finset.sum_congr rfl ?_
  intro L _
  have hL : y + L + (y' - y) = y' + L := by abel
  simp only [Equiv.coe_addLeft, hL]

/-- the composite with mixer M and reset L. -/
def comp (E : G → G) (M : G ≃+ G) (C : G → G) (L : G) : G → G := fun x => C (M (E x) + L)

/-- exact identity: summing the composite's DDT over the reset gives E's DDT row times C's DDT through M. -/
theorem sum_reset_ddt (E : G → G) (M : G ≃+ G) (C : G → G) (α γ : G) :
    ∑ L, ddt (comp E M C L) α γ = ∑ δ, ddt E α δ * ddt C (M δ) γ := by
  have h1 : ∀ L, ddt (comp E M C L) α γ =
      ∑ x, if C (M (E (x + α)) + L) - C (M (E x) + L) = γ then (1 : ℕ) else 0 := by
    intro L; unfold ddt comp; rw [Finset.card_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x, (∑ L, if C (M (E (x + α)) + L) - C (M (E x) + L) = γ then (1 : ℕ) else 0)
      = ddt C (M (E (x + α) - E x)) γ := by
    intro x
    rw [← Finset.card_filter, reset_count C (M (E x)) (M (E (x + α))) γ, map_sub]
  simp_rw [h2]
  rw [← Finset.sum_fiberwise univ (fun x => E (x + α) - E x) (fun x => ddt C (M (E (x + α) - E x)) γ)]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
  rw [Finset.sum_const, smul_eq_mul]
  rfl

/-- key-averaged differential probability of a keyed family. -/
def avgDP {κ : Type*} [Fintype κ] (E : κ → G → G) (α δ : G) : ℝ :=
  (∑ k, (ddt (E k) α δ : ℝ)) / (Fintype.card κ * Fintype.card G)

/-- keyed composite: key (k, c, L), L the reset. -/
def compK {κ κc : Type*} (E : κ → G → G) (M : G ≃+ G) (C : κc → G ≃ G) : κ × κc × G → G → G :=
  fun p => comp (E p.1) M (C p.2.1) p.2.2

theorem col_sum_mixer (C : G ≃ G) (M : G ≃+ G) (γ : G) :
    ∑ δ, (ddt C (M δ) γ : ℝ) = Fintype.card G := by
  have h1 : ∑ δ, (ddt C (M δ) γ : ℝ) = ∑ a, (ddt C a γ : ℝ) :=
    M.toEquiv.sum_comp (fun a => (ddt C a γ : ℝ))
  rw [h1]
  exact_mod_cast ddt_col C γ

theorem suffix_avg_le {κ κc : Type*} [Fintype κ] [Nonempty κ] [Fintype κc] [Nonempty κc]
    (E : κ → G → G) (M : G ≃+ G) (C : κc → G ≃ G) (α : G) (b : ℝ)
    (hE : ∀ δ, avgDP E α δ ≤ b) (γ : G) :
    avgDP (compK E M C) α γ ≤ b := by
  have hA : (0 : ℝ) < Fintype.card κ * Fintype.card G := by positivity
  have hB : (0 : ℝ) < Fintype.card κc * Fintype.card G := by positivity
  -- numerator identity
  have hnum : (∑ p : κ × κc × G, (ddt (compK E M C p) α γ : ℝ))
      = ∑ δ, (∑ k, (ddt (E k) α δ : ℝ)) * (∑ c, (ddt (C c) (M δ) γ : ℝ)) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have h : ∀ k c, (∑ L, (ddt (compK E M C (k, c, L)) α γ : ℝ))
        = ∑ δ, (ddt (E k) α δ : ℝ) * (ddt (C c) (M δ) γ : ℝ) := by
      intro k c
      have := congrArg (Nat.cast : ℕ → ℝ) (sum_reset_ddt (E k) M (C c) α γ)
      push_cast at this
      exact this
    simp_rw [h]
    calc (∑ k, ∑ c, ∑ δ, (ddt (E k) α δ : ℝ) * (ddt (C c) (M δ) γ : ℝ))
        = ∑ k, ∑ δ, ∑ c, (ddt (E k) α δ : ℝ) * (ddt (C c) (M δ) γ : ℝ) :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
      _ = ∑ δ, ∑ k, ∑ c, (ddt (E k) α δ : ℝ) * (ddt (C c) (M δ) γ : ℝ) := Finset.sum_comm
      _ = _ := by simp_rw [Finset.sum_mul_sum]
  have hcol : ∑ δ, (∑ c, (ddt (C c) (M δ) γ : ℝ)) / (Fintype.card κc * Fintype.card G) = 1 := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [col_sum_mixer]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact div_self hB.ne'
  have hden : ((Fintype.card (κ × κc × G) : ℕ) : ℝ) * Fintype.card G
      = (Fintype.card κ * Fintype.card G) * (Fintype.card κc * Fintype.card G) := by
    simp only [Fintype.card_prod]; push_cast; ring
  unfold avgDP
  rw [hnum, hden, Finset.sum_div]
  calc ∑ δ, (∑ k, (ddt (E k) α δ : ℝ)) * (∑ c, (ddt (C c) (M δ) γ : ℝ))
          / ((Fintype.card κ * Fintype.card G) * (Fintype.card κc * Fintype.card G))
      = ∑ δ, avgDP E α δ * ((∑ c, (ddt (C c) (M δ) γ : ℝ)) / (Fintype.card κc * Fintype.card G)) := by
        refine Finset.sum_congr rfl (fun δ _ => ?_)
        unfold avgDP
        rw [mul_div_mul_comm]
    _ ≤ ∑ δ, b * ((∑ c, (ddt (C c) (M δ) γ : ℝ)) / (Fintype.card κc * Fintype.card G)) :=
        Finset.sum_le_sum (fun δ _ => mul_le_mul_of_nonneg_right (hE δ) (by positivity))
    _ = b := by rw [← Finset.mul_sum, hcol, mul_one]

/-- the split tail: two reset post-compositions after E (= E_SB): the averaged bound survives both. -/
theorem four_layer_le {κ κ3 κ4 : Type*} [Fintype κ] [Nonempty κ] [Fintype κ3] [Nonempty κ3]
    [Fintype κ4] [Nonempty κ4]
    (E : κ → G → G) (M2 M3 : G ≃+ G) (C3 : κ3 → G ≃ G) (C4 : κ4 → G ≃ G) (α : G) (b : ℝ)
    (hE : ∀ δ, avgDP E α δ ≤ b) (γ : G) :
    avgDP (compK (compK E M2 C3) M3 C4) α γ ≤ b :=
  suffix_avg_le (compK E M2 C3) M3 C4 α b (suffix_avg_le E M2 C3 α b hE) γ

end ApnCipherC4

end
