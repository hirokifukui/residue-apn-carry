/-
P5-13 (C5, Claude 2026-10-11): ONE component -- the bridge from the REAL key average of the w = 2 superbox
(independent local keys per word, uniform reset L1) to C2's abstract kernel lemma MdsKernel2 (mds2_le),
followed by the C4 reset post-composition (four_layer_le) twice: the (2,2,1,1) split tail, w = 2.
Self-contained: C4 `ResetCompose` (ddt, ddt_col, reset_count, comp, sum_reset_ddt, avgDP, compK,
col_sum_mixer, suffix_avg_le, four_layer_le) and C2 `MdsKernel2` (IsKer, sum_line, K2, unit_neg_mul_eq_zero,
mds2_le) are copied verbatim into namespace ApnCipherC5 (the c2/c4 trees are not touched).
New: avg_comp_eq (exact kernel composition), ddt_row / ddt_zero_row / ddt_to_zero, par / parK / ddt_par,
avgDP_parK (tensor identity of local key products), mix2 (w = 2 mixer as AddEquiv, det a unit), parE,
isKer_avg (averaged DDT of injective local maps is an IsKer kernel), avg_w2_eq (BRIDGE: real average = K2),
w2_split_tail_le (real (2,2,1,1) w = 2 average ≤ ε²).
Inputs that remain hypotheses: the per-word ε-bounds of the local layers (paper: W2, weight-one ρ for ε = 4/N)
and injectivity of the first-layer maps.  NOT formalized: concrete GR(4,m), SHyp/FHyp, general w,
identification of these keyed families with the reference code.
-/
import Mathlib

noncomputable section

open Finset

namespace ApnCipherC5

section RC

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

/-- exact kernel composition: the key-averaged DP of the reset composite is the product of averaged kernels. -/
theorem avg_comp_eq {κ κc : Type*} [Fintype κ] [Nonempty κ] [Fintype κc] [Nonempty κc]
    (E : κ → G → G) (M : G ≃+ G) (C : κc → G ≃ G) (α γ : G) :
    avgDP (compK E M C) α γ = ∑ δ, avgDP E α δ * avgDP (fun c => (C c : G → G)) (M δ) γ := by
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
  have hden : ((Fintype.card (κ × κc × G) : ℕ) : ℝ) * Fintype.card G
      = (Fintype.card κ * Fintype.card G) * (Fintype.card κc * Fintype.card G) := by
    simp only [Fintype.card_prod]; push_cast; ring
  unfold avgDP
  rw [hnum, hden, Finset.sum_div]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  exact mul_div_mul_comm (α := ℝ) _ _ _ _

/-- every DDT row of any map sums to |G|. -/
theorem ddt_row (f : G → G) (a : G) : ∑ b, ddt f a b = Fintype.card G := by
  unfold ddt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem ddt_zero_row (f : G → G) (b : G) :
    ddt f 0 b = if b = 0 then Fintype.card G else 0 := by
  unfold ddt
  by_cases hb : b = 0
  · subst hb; simp
  · simp [hb, Ne.symm hb]

theorem ddt_to_zero (f : G → G) (hf : Function.Injective f) {a : G} (ha : a ≠ 0) :
    ddt f a 0 = 0 := by
  unfold ddt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ h
  apply ha
  have h1 : f (x + a) = f x := sub_eq_zero.mp h
  have h2 : x + a = x + 0 := by rw [add_zero]; exact hf h1
  exact add_left_cancel h2

end RC

section MDS

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- averaged transition kernel of a (keyed) permutation layer whose nonzero rows are bounded by ε. -/
structure IsKer (T : R → R → ℝ) (ε : ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ T a b
  rowsum : ∀ a, ∑ b, T a b = 1
  zero_row : ∀ b, T 0 b = if b = 0 then 1 else 0
  to_zero : ∀ a, a ≠ 0 → T a 0 = 0
  le_eps : ∀ a b, a ≠ 0 → T a b ≤ ε

lemma IsKer.col_zero {T : R → R → ℝ} {ε : ℝ} (h : IsKer T ε) (x : R) :
    T x 0 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; simp [h.zero_row]
  · simp [hx, h.to_zero x hx]

lemma IsKer.le_eps' {T : R → R → ℝ} {ε : ℝ} (h : IsKer T ε) (hε : 0 ≤ ε) (x : R) {g : R}
    (hg : g ≠ 0) : T x g ≤ ε := by
  by_cases hx : x = 0
  · subst hx; simp [h.zero_row, hg, hε]
  · exact h.le_eps x g hx

/-- the line {d2 : m1*d1 + m2*d2 = 0} has exactly one point when m2 is a unit. -/
lemma sum_line (f : R → ℝ) (m1 m2 d1 : R) (hm2 : IsUnit m2) :
    ∑ d2, f d2 * (if m1 * d1 + m2 * d2 = 0 then 1 else 0)
      = f (-(((hm2.unit⁻¹ : Rˣ) : R) * (m1 * d1))) := by
  have key : ∀ d2, (m1 * d1 + m2 * d2 = 0 ↔ d2 = -(((hm2.unit⁻¹ : Rˣ) : R) * (m1 * d1))) := by
    intro d2
    have hu : ((hm2.unit⁻¹ : Rˣ) : R) * m2 = 1 := by simp
    have hu' : m2 * ((hm2.unit⁻¹ : Rˣ) : R) = 1 := by simp
    constructor
    · intro h
      have h2 : m2 * d2 = -(m1 * d1) := by linear_combination h
      calc d2 = (((hm2.unit⁻¹ : Rˣ) : R) * m2) * d2 := by rw [hu, one_mul]
        _ = ((hm2.unit⁻¹ : Rˣ) : R) * (m2 * d2) := by ring
        _ = -(((hm2.unit⁻¹ : Rˣ) : R) * (m1 * d1)) := by rw [h2]; ring
    · intro h
      rw [h]
      linear_combination (-(m1 * d1)) * hu'
  simp_rw [key, mul_ite, mul_one, mul_zero]
  simp

/-- the macro kernel for w = 2. -/
def K2 (T1 T2 U1 U2 : R → R → ℝ) (m11 m12 m21 m22 α1 α2 γ1 γ2 : R) : ℝ :=
  ∑ d1, ∑ d2, T1 α1 d1 * T2 α2 d2 * U1 (m11 * d1 + m12 * d2) γ1 * U2 (m21 * d1 + m22 * d2) γ2

lemma unit_neg_mul_eq_zero {u m d : R} (hu : IsUnit u) (hm : IsUnit m) :
    -(u * (m * d)) = 0 ↔ d = 0 := by
  rw [neg_eq_zero, hu.mul_right_eq_zero, hm.mul_right_eq_zero]

theorem mds2_le {T1 T2 U1 U2 : R → R → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hT1 : IsKer T1 ε) (hT2 : IsKer T2 ε) (hU1 : IsKer U1 ε) (hU2 : IsKer U2 ε)
    {m11 m12 m21 m22 : R} (h11 : IsUnit m11) (h12 : IsUnit m12) (h21 : IsUnit m21)
    (h22 : IsUnit m22) (hdet : IsUnit (m11 * m22 - m12 * m21))
    {α1 α2 : R} (hα : α1 ≠ 0 ∨ α2 ≠ 0) (γ1 γ2 : R) :
    K2 T1 T2 U1 U2 m11 m12 m21 m22 α1 α2 γ1 γ2 ≤ ε ^ 2 := by
  unfold K2
  by_cases g1 : γ1 = 0 <;> by_cases g2 : γ2 = 0
  · -- γ = 0 : every term vanishes (M injective, nonzero α never reaches 0)
    subst g1; subst g2
    have hz : ∀ d1 d2 : R, T1 α1 d1 * T2 α2 d2 * U1 (m11 * d1 + m12 * d2) 0 *
        U2 (m21 * d1 + m22 * d2) 0 = 0 := by
      intro d1 d2
      rw [hU1.col_zero, hU2.col_zero]
      by_cases e1 : m11 * d1 + m12 * d2 = 0 <;> by_cases e2 : m21 * d1 + m22 * d2 = 0
      · have hd1 : (m11 * m22 - m12 * m21) * d1 = 0 := by linear_combination m22 * e1 - m12 * e2
        have hd2 : (m11 * m22 - m12 * m21) * d2 = 0 := by linear_combination m11 * e2 - m21 * e1
        rw [hdet.mul_right_eq_zero] at hd1 hd2
        subst hd1; subst hd2
        rcases hα with h | h
        · simp [hT1.to_zero α1 h]
        · simp [hT2.to_zero α2 h]
      · simp [e2]
      · simp [e1]
      · simp [e1]
    simp [hz]
    positivity
  · -- γ1 = 0, γ2 ≠ 0 : constraint (Md)_1 = 0
    subst g1
    have step : ∀ d1 d2 : R, T1 α1 d1 * T2 α2 d2 * U1 (m11 * d1 + m12 * d2) 0 *
        U2 (m21 * d1 + m22 * d2) γ2 ≤
        ε * (T1 α1 d1 * (T2 α2 d2 * (if m11 * d1 + m12 * d2 = 0 then 1 else 0))) := by
      intro d1 d2
      rw [hU1.col_zero]
      have u2 := hU2.le_eps' hε (m21 * d1 + m22 * d2) g2
      have n1 := hT1.nonneg α1 d1; have n2 := hT2.nonneg α2 d2
      split_ifs <;> nlinarith [mul_nonneg n1 n2]
    calc _ ≤ ∑ d1, ∑ d2, ε * (T1 α1 d1 * (T2 α2 d2 * (if m11 * d1 + m12 * d2 = 0 then 1 else 0))) :=
          sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => step d1 d2
      _ = ∑ d1, ε * (T1 α1 d1 * T2 α2 (-(((h12.unit⁻¹ : Rˣ) : R) * (m11 * d1)))) := by
          refine sum_congr rfl fun d1 _ => ?_
          rw [← mul_sum, ← mul_sum, sum_line (T2 α2) m11 m12 d1 h12]
      _ ≤ ε ^ 2 := by
          by_cases a2 : α2 = 0
          · have a1 : α1 ≠ 0 := by rcases hα with h | h; exact h; exact absurd a2 h
            subst a2
            have hz : ∀ d1 : R, T1 α1 d1 * T2 0 (-(((h12.unit⁻¹ : Rˣ) : R) * (m11 * d1))) = 0 := by
              intro d1
              rw [hT2.zero_row]
              by_cases hd : d1 = 0
              · subst hd; simp [hT1.to_zero α1 a1]
              · have : ¬ (-(((h12.unit⁻¹ : Rˣ) : R) * (m11 * d1)) = 0) := by
                  rw [unit_neg_mul_eq_zero (Units.isUnit _) h11]; exact hd
                simp [this]
            simp [hz]; positivity
          · have b : ∀ d1 : R, ε * (T1 α1 d1 * T2 α2 (-(((h12.unit⁻¹ : Rˣ) : R) * (m11 * d1))))
                ≤ ε * (T1 α1 d1 * ε) := by
              intro d1
              apply mul_le_mul_of_nonneg_left _ hε
              exact mul_le_mul_of_nonneg_left (hT2.le_eps _ _ a2) (hT1.nonneg _ _)
            calc _ ≤ ∑ d1, ε * (T1 α1 d1 * ε) := sum_le_sum fun d1 _ => b d1
              _ = ε ^ 2 := by
                rw [← mul_sum, ← sum_mul, hT1.rowsum]; ring
  · -- γ1 ≠ 0, γ2 = 0 : constraint (Md)_2 = 0
    subst g2
    have step : ∀ d1 d2 : R, T1 α1 d1 * T2 α2 d2 * U1 (m11 * d1 + m12 * d2) γ1 *
        U2 (m21 * d1 + m22 * d2) 0 ≤
        ε * (T1 α1 d1 * (T2 α2 d2 * (if m21 * d1 + m22 * d2 = 0 then 1 else 0))) := by
      intro d1 d2
      rw [hU2.col_zero]
      have u1 := hU1.le_eps' hε (m11 * d1 + m12 * d2) g1
      have n1 := hT1.nonneg α1 d1; have n2 := hT2.nonneg α2 d2
      split_ifs <;> nlinarith [mul_nonneg n1 n2]
    calc _ ≤ ∑ d1, ∑ d2, ε * (T1 α1 d1 * (T2 α2 d2 * (if m21 * d1 + m22 * d2 = 0 then 1 else 0))) :=
          sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => step d1 d2
      _ = ∑ d1, ε * (T1 α1 d1 * T2 α2 (-(((h22.unit⁻¹ : Rˣ) : R) * (m21 * d1)))) := by
          refine sum_congr rfl fun d1 _ => ?_
          rw [← mul_sum, ← mul_sum, sum_line (T2 α2) m21 m22 d1 h22]
      _ ≤ ε ^ 2 := by
          by_cases a2 : α2 = 0
          · have a1 : α1 ≠ 0 := by rcases hα with h | h; exact h; exact absurd a2 h
            subst a2
            have hz : ∀ d1 : R, T1 α1 d1 * T2 0 (-(((h22.unit⁻¹ : Rˣ) : R) * (m21 * d1))) = 0 := by
              intro d1
              rw [hT2.zero_row]
              by_cases hd : d1 = 0
              · subst hd; simp [hT1.to_zero α1 a1]
              · have : ¬ (-(((h22.unit⁻¹ : Rˣ) : R) * (m21 * d1)) = 0) := by
                  rw [unit_neg_mul_eq_zero (Units.isUnit _) h21]; exact hd
                simp [this]
            simp [hz]; positivity
          · have b : ∀ d1 : R, ε * (T1 α1 d1 * T2 α2 (-(((h22.unit⁻¹ : Rˣ) : R) * (m21 * d1))))
                ≤ ε * (T1 α1 d1 * ε) := by
              intro d1
              apply mul_le_mul_of_nonneg_left _ hε
              exact mul_le_mul_of_nonneg_left (hT2.le_eps _ _ a2) (hT1.nonneg _ _)
            calc _ ≤ ∑ d1, ε * (T1 α1 d1 * ε) := sum_le_sum fun d1 _ => b d1
              _ = ε ^ 2 := by
                rw [← mul_sum, ← sum_mul, hT1.rowsum]; ring
  · -- γ1 ≠ 0, γ2 ≠ 0 : both output kernels bounded by ε
    have step : ∀ d1 d2 : R, T1 α1 d1 * T2 α2 d2 * U1 (m11 * d1 + m12 * d2) γ1 *
        U2 (m21 * d1 + m22 * d2) γ2 ≤ T1 α1 d1 * T2 α2 d2 * (ε * ε) := by
      intro d1 d2
      have u1 := hU1.le_eps' hε (m11 * d1 + m12 * d2) g1
      have u2 := hU2.le_eps' hε (m21 * d1 + m22 * d2) g2
      have n := mul_nonneg (hT1.nonneg α1 d1) (hT2.nonneg α2 d2)
      have uu := mul_le_mul u1 u2 (hU2.nonneg _ _) hε
      calc _ = T1 α1 d1 * T2 α2 d2 * (U1 (m11 * d1 + m12 * d2) γ1 * U2 (m21 * d1 + m22 * d2) γ2) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left uu n
    have e : ∀ d1 : R, ∑ d2, T1 α1 d1 * T2 α2 d2 * (ε * ε) = T1 α1 d1 * (ε * ε) := by
      intro d1
      rw [← sum_mul, ← mul_sum, hT2.rowsum, mul_one]
    calc _ ≤ ∑ d1, ∑ d2, T1 α1 d1 * T2 α2 d2 * (ε * ε) :=
          sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => step d1 d2
      _ = ∑ d1, T1 α1 d1 * (ε * ε) := sum_congr rfl fun d1 _ => e d1
      _ = ε ^ 2 := by rw [← sum_mul, hT1.rowsum]; ring

end MDS

section W2

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- two-word parallel map. -/
def par (f g : R → R) : R × R → R × R := fun x => (f x.1, g x.2)

theorem ddt_par (f g : R → R) (α γ : R × R) :
    ddt (par f g) α γ = ddt f α.1 γ.1 * ddt g α.2 γ.2 := by
  unfold ddt
  have h : (univ.filter (fun x : R × R => par f g (x + α) - par f g x = γ)) =
      (univ.filter (fun a : R => f (a + α.1) - f a = γ.1)) ×ˢ
        (univ.filter (fun b : R => g (b + α.2) - g b = γ.2)) := by
    ext ⟨a, b⟩
    simp [par, Prod.ext_iff]
  rw [h, Finset.card_product]

/-- independent local keys (product key space). -/
def parK {κ1 κ2 : Type*} (f : κ1 → R → R) (g : κ2 → R → R) : κ1 × κ2 → R × R → R × R :=
  fun k => par (f k.1) (g k.2)

/-- tensor identity: the key-averaged DP of the parallel layer is the product of the local averaged DPs. -/
theorem avgDP_parK {κ1 κ2 : Type*} [Fintype κ1] [Fintype κ2]
    (f : κ1 → R → R) (g : κ2 → R → R) (α δ : R × R) :
    avgDP (parK f g) α δ = avgDP f α.1 δ.1 * avgDP g α.2 δ.2 := by
  unfold avgDP
  rw [div_mul_div_comm]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp [parK, ddt_par]
  · simp only [Fintype.card_prod]
    push_cast
    ring

/-- the w = 2 mixer as an additive automorphism (entries arbitrary, determinant a unit). -/
def mix2 (m11 m12 m21 m22 : R) (hdet : IsUnit (m11 * m22 - m12 * m21)) : (R × R) ≃+ (R × R) where
  toFun d := (m11 * d.1 + m12 * d.2, m21 * d.1 + m22 * d.2)
  invFun e := (((hdet.unit⁻¹ : Rˣ) : R) * (m22 * e.1 - m12 * e.2),
               ((hdet.unit⁻¹ : Rˣ) : R) * (m11 * e.2 - m21 * e.1))
  left_inv d := by
    have hu : ((hdet.unit⁻¹ : Rˣ) : R) * (m11 * m22 - m12 * m21) = 1 := by simp
    refine Prod.ext ?_ ?_
    · dsimp only
      linear_combination d.1 * hu
    · dsimp only
      linear_combination d.2 * hu
  right_inv e := by
    have hu : (m11 * m22 - m12 * m21) * ((hdet.unit⁻¹ : Rˣ) : R) = 1 := by simp
    refine Prod.ext ?_ ?_
    · dsimp only
      linear_combination e.1 * hu
    · dsimp only
      linear_combination e.2 * hu
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]; ring
    · simp only [Prod.fst_add, Prod.snd_add]; ring

theorem mix2_apply (m11 m12 m21 m22 : R) (hdet : IsUnit (m11 * m22 - m12 * m21)) (d : R × R) :
    mix2 m11 m12 m21 m22 hdet d = (m11 * d.1 + m12 * d.2, m21 * d.1 + m22 * d.2) := rfl

/-- second local layer: independent keyed permutations per word. -/
def parE {κ3 κ4 : Type*} (g1 : κ3 → R ≃ R) (g2 : κ4 → R ≃ R) : κ3 × κ4 → (R × R) ≃ (R × R) :=
  fun j => (g1 j.1).prodCongr (g2 j.2)

theorem parE_coe {κ3 κ4 : Type*} (g1 : κ3 → R ≃ R) (g2 : κ4 → R ≃ R) :
    (fun c => (parE g1 g2 c : R × R → R × R)) =
      parK (fun k => (g1 k : R → R)) (fun k => (g2 k : R → R)) := by
  funext c x
  refine Prod.ext ?_ ?_ <;> simp [parE, parK, par]

/-- the averaged DP of a family of injective local maps is a C2 kernel (IsKer); only the ε-bound is an input. -/
theorem isKer_avg {κ : Type*} [Fintype κ] [Nonempty κ] (F : κ → R → R)
    (hF : ∀ k, Function.Injective (F k)) {ε : ℝ}
    (hle : ∀ a b, a ≠ 0 → avgDP F a b ≤ ε) : IsKer (avgDP F) ε := by
  have hpos : (0 : ℝ) < Fintype.card κ * Fintype.card R := by positivity
  refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_, fun a ha => ?_, hle⟩
  · unfold avgDP; positivity
  · unfold avgDP
    rw [← Finset.sum_div, Finset.sum_comm]
    have h : ∀ k, ∑ b, (ddt (F k) a b : ℝ) = Fintype.card R := fun k => by
      exact_mod_cast ddt_row (F k) a
    simp_rw [h]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact div_self hpos.ne'
  · unfold avgDP
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl]
      have h : ∀ k, (ddt (F k) 0 0 : ℝ) = Fintype.card R := fun k => by
        rw [ddt_zero_row]; simp
      simp_rw [h]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact div_self hpos.ne'
    · have h : ∀ k, (ddt (F k) 0 b : ℝ) = 0 := fun k => by
        rw [ddt_zero_row, if_neg hb]; simp
      simp [h, hb]
  · unfold avgDP
    have h : ∀ k, ddt (F k) a 0 = 0 := fun k => ddt_to_zero (F k) (hF k) ha
    simp [h]

/-- BRIDGE: the real key-averaged DP of the w = 2 superbox (independent local keys, uniform reset L1)
equals the C2 kernel K2 built from the local averaged DDTs. -/
theorem avg_w2_eq {κ1 κ2 κ3 κ4 : Type*} [Fintype κ1] [Nonempty κ1] [Fintype κ2] [Nonempty κ2]
    [Fintype κ3] [Nonempty κ3] [Fintype κ4] [Nonempty κ4]
    (F1 : κ1 → R → R) (F2 : κ2 → R → R) (g1 : κ3 → R ≃ R) (g2 : κ4 → R ≃ R)
    (m11 m12 m21 m22 : R) (hdet : IsUnit (m11 * m22 - m12 * m21)) (α γ : R × R) :
    avgDP (compK (parK F1 F2) (mix2 m11 m12 m21 m22 hdet) (parE g1 g2)) α γ =
      K2 (avgDP F1) (avgDP F2) (avgDP (fun k => (g1 k : R → R))) (avgDP (fun k => (g2 k : R → R)))
        m11 m12 m21 m22 α.1 α.2 γ.1 γ.2 := by
  rw [avg_comp_eq, parE_coe]
  simp_rw [avgDP_parK]
  rw [Fintype.sum_prod_type]
  unfold K2
  refine Finset.sum_congr rfl (fun d1 _ => Finset.sum_congr rfl (fun d2 _ => ?_))
  simp only [mix2_apply]
  ring

/-- w = 2 split tail (2,2,1,1): real key average ≤ ε² for every nonzero input difference.
Inputs: the four local ε-bounds (paper: W2) and injectivity of the first-layer maps. -/
theorem w2_split_tail_le {κ1 κ2 κ3 κ4 κ5 κ6 : Type*} [Fintype κ1] [Nonempty κ1]
    [Fintype κ2] [Nonempty κ2] [Fintype κ3] [Nonempty κ3] [Fintype κ4] [Nonempty κ4]
    [Fintype κ5] [Nonempty κ5] [Fintype κ6] [Nonempty κ6]
    (F1 : κ1 → R → R) (F2 : κ2 → R → R) (g1 : κ3 → R ≃ R) (g2 : κ4 → R ≃ R)
    (hF1 : ∀ k, Function.Injective (F1 k)) (hF2 : ∀ k, Function.Injective (F2 k))
    {m11 m12 m21 m22 : R} (h11 : IsUnit m11) (h12 : IsUnit m12) (h21 : IsUnit m21)
    (h22 : IsUnit m22) (hdet : IsUnit (m11 * m22 - m12 * m21))
    (M2 M3 : (R × R) ≃+ (R × R)) (C3 : κ5 → (R × R) ≃ (R × R)) (C4 : κ6 → (R × R) ≃ (R × R))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hb1 : ∀ a b, a ≠ 0 → avgDP F1 a b ≤ ε) (hb2 : ∀ a b, a ≠ 0 → avgDP F2 a b ≤ ε)
    (hb3 : ∀ a b, a ≠ 0 → avgDP (fun k => (g1 k : R → R)) a b ≤ ε)
    (hb4 : ∀ a b, a ≠ 0 → avgDP (fun k => (g2 k : R → R)) a b ≤ ε)
    {α : R × R} (hα : α ≠ 0) (γ : R × R) :
    avgDP (compK (compK (compK (parK F1 F2) (mix2 m11 m12 m21 m22 hdet) (parE g1 g2)) M2 C3) M3 C4)
      α γ ≤ ε ^ 2 := by
  have hα' : α.1 ≠ 0 ∨ α.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hα (Prod.ext h.1 h.2)
  refine four_layer_le _ M2 M3 C3 C4 α (ε ^ 2) (fun δ => ?_) γ
  rw [avg_w2_eq]
  exact mds2_le hε (isKer_avg F1 hF1 hb1) (isKer_avg F2 hF2 hb2)
    (isKer_avg (fun k => (g1 k : R → R)) (fun k => (g1 k).injective) hb3)
    (isKer_avg (fun k => (g2 k : R → R)) (fun k => (g2 k).injective) hb4)
    h11 h12 h21 h22 hdet hα' δ.1 δ.2

end W2

end ApnCipherC5

end
