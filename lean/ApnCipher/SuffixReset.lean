/-
P3-14 part 1 (C3, Claude 2026-10-10): the post-composition (suffix) lemma with an independent reset, on any finite
additive commutative group G (e.g. R^w with R = GR(4,m)).  Real DDT counts, no abstract kernel hypotheses.
  ddt f a b = #{x | f (x + a) - f x = b}.
  * ddt_row  : Σ_b ddt f a b = |G|                (any map f)
  * ddt_col  : Σ_a ddt f a b = |G|                (f a permutation)
  * reset_count : for fixed points y, y', #{L | C (y' + L) - C (y + L) = γ} = ddt C (y' - y) γ
                 (averaging over the independent uniform reset L turns ANY pair with difference y' - y into the DDT row)
  * suffix_le : if every entry k β of a (key-averaged) row is ≤ c, then for a permutation C and a relabelling e
                (the linear mixer M2), Σ_β k β · ddt C (e β) γ / |G| ≤ c.
Not formalized here: the probability space of the C2 macro keys and the identification of k with K_SB(α, ·)
(paper: SUFFIX_KERNEL_P3.md; abstract D1 is C2's MdsKernel2).
-/
import Mathlib

noncomputable section

namespace ApnCipherC3

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- DDT count of a map on a finite additive group. -/
def ddt (f : G → G) (a b : G) : ℕ := (univ.filter (fun x => f (x + a) - f x = b)).card

theorem ddt_row (f : G → G) (a : G) : ∑ b, ddt f a b = Fintype.card G := by
  unfold ddt
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun x => f (x + a) - f x) (by simp)).symm

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

/-- normalized DDT column sums are 1 (permutation C), also after a relabelling e of the input differences. -/
theorem ddt_col_norm (C : G ≃ G) (e : G ≃ G) (γ : G) :
    ∑ β, (ddt C (e β) γ : ℝ) / Fintype.card G = 1 := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this.ne'
  rw [← Finset.sum_div]
  rw [div_eq_one_iff_eq hG]
  have h1 := e.sum_comp (fun a => (ddt C a γ : ℝ))
  rw [h1]
  exact_mod_cast ddt_col C γ

/-- the suffix lemma: a row bounded entrywise by c stays bounded by c after M2 (relabelling e) and a reset + permutation C. -/
theorem suffix_le (C : G ≃ G) (e : G ≃ G) (k : G → ℝ) (c : ℝ) (hk : ∀ β, k β ≤ c) (γ : G) :
    ∑ β, k β * ((ddt C (e β) γ : ℝ) / Fintype.card G) ≤ c := by
  have hT : ∀ β, 0 ≤ (ddt C (e β) γ : ℝ) / Fintype.card G := fun β => by positivity
  calc ∑ β, k β * ((ddt C (e β) γ : ℝ) / Fintype.card G)
      ≤ ∑ β, c * ((ddt C (e β) γ : ℝ) / Fintype.card G) :=
        Finset.sum_le_sum (fun β _ => mul_le_mul_of_nonneg_right (hk β) (hT β))
    _ = c := by rw [← Finset.mul_sum, ddt_col_norm C e γ, mul_one]

end ApnCipherC3

end
