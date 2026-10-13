/-
P9-03 (C9, Claude 2026-10-12): ONE component -- the two-word MDS kernel lemma over a finite ADDITIVE group,
with the mixer an additive automorphism M of A × A whose four partial maps
  c11 x = (M (x,0)).1,  c12 y = (M (0,y)).1,  c21 x = (M (x,0)).2,  c22 y = (M (0,y)).2
are bijective (no ring, no scalar multiplication).  This replaces the ring-scalar hypotheses of C2/C5
`mds2_le` / `w2_split_tail_le`, which on the pointwise ring (ZMod 4)^m have no instance (VacuousZ4.lean).
Proof = the four cases of C5 `mds2_le` (γ = 0; γ1 = 0; γ2 = 0; both nonzero) with the unit inverse replaced
by the inverse of a bijective additive map.
Also: additive copies of C5 par / parK / avgDP_parK / parE / isKer_avg / avg_w2_eq (C5 states them for a
CommRing R but uses only +), and the (2,2,1,1) split tail `w2A_split_tail_le`.
C5's ddt, avgDP, compK, avg_comp_eq, four_layer_le, ddt_row, ddt_zero_row, ddt_to_zero are already stated
for an AddCommGroup and are reused unchanged.
-/
import ApnCipher.W2Bridge

noncomputable section

open Finset

namespace ApnCipherC9

section MixAdd

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- averaged transition kernel (C2 IsKer, additive group version). -/
structure IsKerA (T : A → A → ℝ) (ε : ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ T a b
  rowsum : ∀ a, ∑ b, T a b = 1
  zero_row : ∀ b, T 0 b = if b = 0 then 1 else 0
  to_zero : ∀ a, a ≠ 0 → T a 0 = 0
  le_eps : ∀ a b, a ≠ 0 → T a b ≤ ε

lemma IsKerA.col_zero {T : A → A → ℝ} {ε : ℝ} (h : IsKerA T ε) (x : A) :
    T x 0 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; simp [h.zero_row]
  · simp [hx, h.to_zero x hx]

lemma IsKerA.le_eps' {T : A → A → ℝ} {ε : ℝ} (h : IsKerA T ε) (hε : 0 ≤ ε) (x : A) {g : A}
    (hg : g ≠ 0) : T x g ≤ ε := by
  by_cases hx : x = 0
  · subst hx; simp [h.zero_row, hg, hε]
  · exact h.le_eps x g hx

/-- the four partial maps of an additive mixer. -/
def c11 (M : (A × A) ≃+ (A × A)) : A →+ A :=
  (AddMonoidHom.fst A A).comp (M.toAddMonoidHom.comp (AddMonoidHom.inl A A))
def c12 (M : (A × A) ≃+ (A × A)) : A →+ A :=
  (AddMonoidHom.fst A A).comp (M.toAddMonoidHom.comp (AddMonoidHom.inr A A))
def c21 (M : (A × A) ≃+ (A × A)) : A →+ A :=
  (AddMonoidHom.snd A A).comp (M.toAddMonoidHom.comp (AddMonoidHom.inl A A))
def c22 (M : (A × A) ≃+ (A × A)) : A →+ A :=
  (AddMonoidHom.snd A A).comp (M.toAddMonoidHom.comp (AddMonoidHom.inr A A))

lemma pair_split (d1 d2 : A) : ((d1, d2) : A × A) = (d1, 0) + (0, d2) := by
  ext <;> simp

theorem M_fst (M : (A × A) ≃+ (A × A)) (d1 d2 : A) :
    (M (d1, d2)).1 = c11 M d1 + c12 M d2 := by
  rw [pair_split d1 d2, map_add]
  simp [c11, c12]

theorem M_snd (M : (A × A) ≃+ (A × A)) (d1 d2 : A) :
    (M (d1, d2)).2 = c21 M d1 + c22 M d2 := by
  rw [pair_split d1 d2, map_add]
  simp [c21, c22]

/-- two-word MDS condition for an additive mixer: all four partial maps are bijective. -/
structure IsMDS2A (M : (A × A) ≃+ (A × A)) : Prop where
  b11 : Function.Bijective (c11 M)
  b12 : Function.Bijective (c12 M)
  b21 : Function.Bijective (c21 M)
  b22 : Function.Bijective (c22 M)

/-- the line {d2 : a d1 + b d2 = 0} has exactly one point when b is bijective. -/
lemma sum_lineA (f : A → ℝ) (a b : A →+ A) (hb : Function.Bijective b) (d1 : A) :
    ∑ d2, f d2 * (if a d1 + b d2 = 0 then 1 else 0)
      = f ((Equiv.ofBijective b hb).symm (-(a d1))) := by
  set e := Equiv.ofBijective b hb
  have key : ∀ d2, (a d1 + b d2 = 0 ↔ d2 = e.symm (-(a d1))) := by
    intro d2
    constructor
    · intro h
      have h2 : b d2 = -(a d1) := by
        rw [add_comm] at h
        exact eq_neg_of_add_eq_zero_left h
      rw [← h2]
      have : e d2 = b d2 := rfl
      rw [← this, Equiv.symm_apply_apply]
    · intro h
      have h3 : b d2 = -(a d1) := by
        rw [h]
        exact Equiv.ofBijective_apply_symm_apply b hb _
      rw [h3]
      exact add_neg_cancel _
  simp_rw [key, mul_ite, mul_one, mul_zero]
  simp

/-- the half case (exactly one output word is zero): at most ε². -/
lemma half_case {T1 T2 : A → A → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hT1 : IsKerA T1 ε) (hT2 : IsKerA T2 ε)
    (a b : A →+ A) (ha : Function.Injective a) (hb : Function.Bijective b)
    {α1 α2 : A} (hα : α1 ≠ 0 ∨ α2 ≠ 0) :
    ∑ d1, ∑ d2, ε * (T1 α1 d1 * (T2 α2 d2 * (if a d1 + b d2 = 0 then 1 else 0))) ≤ ε ^ 2 := by
  set e := Equiv.ofBijective b hb
  calc _ = ∑ d1, ε * (T1 α1 d1 * T2 α2 (e.symm (-(a d1)))) := by
          refine sum_congr rfl fun d1 _ => ?_
          rw [← mul_sum, ← mul_sum, sum_lineA (T2 α2) a b hb d1]
    _ ≤ ε ^ 2 := by
          by_cases a2 : α2 = 0
          · have a1 : α1 ≠ 0 := by rcases hα with h | h; exact h; exact absurd a2 h
            subst a2
            have hz : ∀ d1 : A, T1 α1 d1 * T2 0 (e.symm (-(a d1))) = 0 := by
              intro d1
              rw [hT2.zero_row]
              by_cases hd : d1 = 0
              · subst hd; simp [hT1.to_zero α1 a1]
              · have : ¬ (e.symm (-(a d1)) = 0) := by
                  intro h0
                  have h1 : e (e.symm (-(a d1))) = e 0 := by rw [h0]
                  rw [Equiv.apply_symm_apply] at h1
                  have h2 : e 0 = 0 := map_zero b
                  rw [h2, neg_eq_zero] at h1
                  exact hd (ha (h1.trans (map_zero a).symm))
                simp [this]
            simp [hz]; positivity
          · have bnd : ∀ d1 : A, ε * (T1 α1 d1 * T2 α2 (e.symm (-(a d1))))
                ≤ ε * (T1 α1 d1 * ε) := by
              intro d1
              apply mul_le_mul_of_nonneg_left _ hε
              exact mul_le_mul_of_nonneg_left (hT2.le_eps _ _ a2) (hT1.nonneg _ _)
            calc _ ≤ ∑ d1, ε * (T1 α1 d1 * ε) := sum_le_sum fun d1 _ => bnd d1
              _ = ε ^ 2 := by
                rw [← mul_sum, ← sum_mul, hT1.rowsum]; ring

/-- the w = 2 kernel through an additive mixer. -/
def K2A (T1 T2 U1 U2 : A → A → ℝ) (M : (A × A) ≃+ (A × A)) (α γ : A × A) : ℝ :=
  ∑ d1, ∑ d2, T1 α.1 d1 * T2 α.2 d2 * U1 (M (d1, d2)).1 γ.1 * U2 (M (d1, d2)).2 γ.2

/-- MDS kernel lemma over an additive group: K2A ≤ ε² for every nonzero input difference. -/
theorem mds2A_le {T1 T2 U1 U2 : A → A → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hT1 : IsKerA T1 ε) (hT2 : IsKerA T2 ε) (hU1 : IsKerA U1 ε) (hU2 : IsKerA U2 ε)
    (M : (A × A) ≃+ (A × A)) (hM : IsMDS2A M)
    {α : A × A} (hα : α ≠ 0) (γ : A × A) :
    K2A T1 T2 U1 U2 M α γ ≤ ε ^ 2 := by
  have hα' : α.1 ≠ 0 ∨ α.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hα (Prod.ext h.1 h.2)
  unfold K2A
  simp_rw [M_fst, M_snd]
  obtain ⟨γ1, γ2⟩ := γ
  obtain ⟨α1, α2⟩ := α
  simp only at hα' ⊢
  by_cases g1 : γ1 = 0 <;> by_cases g2 : γ2 = 0
  · -- γ = 0 : M injective and α ≠ 0
    subst g1; subst g2
    have hz : ∀ d1 d2 : A, T1 α1 d1 * T2 α2 d2 * U1 (c11 M d1 + c12 M d2) 0 *
        U2 (c21 M d1 + c22 M d2) 0 = 0 := by
      intro d1 d2
      rw [hU1.col_zero, hU2.col_zero]
      by_cases e1 : c11 M d1 + c12 M d2 = 0 <;> by_cases e2 : c21 M d1 + c22 M d2 = 0
      · have hMd : M (d1, d2) = M 0 := by
          rw [map_zero]
          exact Prod.ext (by rw [M_fst]; exact e1) (by rw [M_snd]; exact e2)
        have hd := M.injective hMd
        have hd1 : d1 = 0 := congrArg Prod.fst hd
        have hd2 : d2 = 0 := congrArg Prod.snd hd
        subst hd1; subst hd2
        rcases hα' with h | h
        · simp [hT1.to_zero α1 h]
        · simp [hT2.to_zero α2 h]
      · simp [e2]
      · simp [e1]
      · simp [e1]
    simp [hz]
    positivity
  · -- γ1 = 0, γ2 ≠ 0
    subst g1
    have step : ∀ d1 d2 : A, T1 α1 d1 * T2 α2 d2 * U1 (c11 M d1 + c12 M d2) 0 *
        U2 (c21 M d1 + c22 M d2) γ2 ≤
        ε * (T1 α1 d1 * (T2 α2 d2 * (if c11 M d1 + c12 M d2 = 0 then 1 else 0))) := by
      intro d1 d2
      rw [hU1.col_zero]
      have u2 := hU2.le_eps' hε (c21 M d1 + c22 M d2) g2
      have n1 := hT1.nonneg α1 d1; have n2 := hT2.nonneg α2 d2
      split_ifs <;> nlinarith [mul_nonneg n1 n2]
    calc _ ≤ ∑ d1, ∑ d2, ε * (T1 α1 d1 * (T2 α2 d2 *
              (if c11 M d1 + c12 M d2 = 0 then 1 else 0))) :=
          sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => step d1 d2
      _ ≤ ε ^ 2 := half_case hε hT1 hT2 (c11 M) (c12 M) hM.b11.1 hM.b12 hα'
  · -- γ1 ≠ 0, γ2 = 0
    subst g2
    have step : ∀ d1 d2 : A, T1 α1 d1 * T2 α2 d2 * U1 (c11 M d1 + c12 M d2) γ1 *
        U2 (c21 M d1 + c22 M d2) 0 ≤
        ε * (T1 α1 d1 * (T2 α2 d2 * (if c21 M d1 + c22 M d2 = 0 then 1 else 0))) := by
      intro d1 d2
      rw [hU2.col_zero]
      have u1 := hU1.le_eps' hε (c11 M d1 + c12 M d2) g1
      have n1 := hT1.nonneg α1 d1; have n2 := hT2.nonneg α2 d2
      split_ifs <;> nlinarith [mul_nonneg n1 n2]
    calc _ ≤ ∑ d1, ∑ d2, ε * (T1 α1 d1 * (T2 α2 d2 *
              (if c21 M d1 + c22 M d2 = 0 then 1 else 0))) :=
          sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => step d1 d2
      _ ≤ ε ^ 2 := half_case hε hT1 hT2 (c21 M) (c22 M) hM.b21.1 hM.b22 hα'
  · -- both output words nonzero
    have step : ∀ d1 d2 : A, T1 α1 d1 * T2 α2 d2 * U1 (c11 M d1 + c12 M d2) γ1 *
        U2 (c21 M d1 + c22 M d2) γ2 ≤ T1 α1 d1 * T2 α2 d2 * (ε * ε) := by
      intro d1 d2
      have u1 := hU1.le_eps' hε (c11 M d1 + c12 M d2) g1
      have u2 := hU2.le_eps' hε (c21 M d1 + c22 M d2) g2
      have n := mul_nonneg (hT1.nonneg α1 d1) (hT2.nonneg α2 d2)
      have uu := mul_le_mul u1 u2 (hU2.nonneg _ _) hε
      calc _ = T1 α1 d1 * T2 α2 d2 * (U1 (c11 M d1 + c12 M d2) γ1 * U2 (c21 M d1 + c22 M d2) γ2) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left uu n
    have e : ∀ d1 : A, ∑ d2, T1 α1 d1 * T2 α2 d2 * (ε * ε) = T1 α1 d1 * (ε * ε) := by
      intro d1
      rw [← sum_mul, ← mul_sum, hT2.rowsum, mul_one]
    calc _ ≤ ∑ d1, ∑ d2, T1 α1 d1 * T2 α2 d2 * (ε * ε) :=
          sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => step d1 d2
      _ = ∑ d1, T1 α1 d1 * (ε * ε) := sum_congr rfl fun d1 _ => e d1
      _ = ε ^ 2 := by rw [← sum_mul, hT1.rowsum]; ring

/-! ### the real key average (additive copies of C5 W2 section) -/

/-- two-word parallel map. -/
def parA (f g : A → A) : A × A → A × A := fun x => (f x.1, g x.2)

theorem ddt_parA (f g : A → A) (α γ : A × A) :
    ApnCipherC5.ddt (parA f g) α γ = ApnCipherC5.ddt f α.1 γ.1 * ApnCipherC5.ddt g α.2 γ.2 := by
  unfold ApnCipherC5.ddt
  have h : (univ.filter (fun x : A × A => parA f g (x + α) - parA f g x = γ)) =
      (univ.filter (fun a : A => f (a + α.1) - f a = γ.1)) ×ˢ
        (univ.filter (fun b : A => g (b + α.2) - g b = γ.2)) := by
    ext ⟨a, b⟩
    simp [parA, Prod.ext_iff]
  rw [h, Finset.card_product]

/-- independent local keys (product key space). -/
def parKA {κ1 κ2 : Type*} (f : κ1 → A → A) (g : κ2 → A → A) : κ1 × κ2 → A × A → A × A :=
  fun k => parA (f k.1) (g k.2)

theorem avgDP_parKA {κ1 κ2 : Type*} [Fintype κ1] [Fintype κ2]
    (f : κ1 → A → A) (g : κ2 → A → A) (α δ : A × A) :
    ApnCipherC5.avgDP (parKA f g) α δ = ApnCipherC5.avgDP f α.1 δ.1 * ApnCipherC5.avgDP g α.2 δ.2 := by
  unfold ApnCipherC5.avgDP
  rw [div_mul_div_comm]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp [parKA, ddt_parA]
  · simp only [Fintype.card_prod]
    push_cast
    ring

/-- second local layer: independent keyed permutations per word. -/
def parEA {κ3 κ4 : Type*} (g1 : κ3 → A ≃ A) (g2 : κ4 → A ≃ A) : κ3 × κ4 → (A × A) ≃ (A × A) :=
  fun j => (g1 j.1).prodCongr (g2 j.2)

theorem parEA_coe {κ3 κ4 : Type*} (g1 : κ3 → A ≃ A) (g2 : κ4 → A ≃ A) :
    (fun c => (parEA g1 g2 c : A × A → A × A)) =
      parKA (fun k => (g1 k : A → A)) (fun k => (g2 k : A → A)) := by
  funext c x
  refine Prod.ext ?_ ?_ <;> simp [parEA, parKA, parA]

theorem isKerA_avg {κ : Type*} [Fintype κ] [Nonempty κ] (F : κ → A → A)
    (hF : ∀ k, Function.Injective (F k)) {ε : ℝ}
    (hle : ∀ a b, a ≠ 0 → ApnCipherC5.avgDP F a b ≤ ε) : IsKerA (ApnCipherC5.avgDP F) ε := by
  have hpos : (0 : ℝ) < Fintype.card κ * Fintype.card A := by positivity
  refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_, fun a ha => ?_, hle⟩
  · unfold ApnCipherC5.avgDP; positivity
  · unfold ApnCipherC5.avgDP
    rw [← Finset.sum_div, Finset.sum_comm]
    have h : ∀ k, ∑ b, (ApnCipherC5.ddt (F k) a b : ℝ) = Fintype.card A := fun k => by
      exact_mod_cast ApnCipherC5.ddt_row (F k) a
    simp_rw [h]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact div_self hpos.ne'
  · unfold ApnCipherC5.avgDP
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl]
      have h : ∀ k, (ApnCipherC5.ddt (F k) 0 0 : ℝ) = Fintype.card A := fun k => by
        rw [ApnCipherC5.ddt_zero_row]; simp
      simp_rw [h]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact div_self hpos.ne'
    · have h : ∀ k, (ApnCipherC5.ddt (F k) 0 b : ℝ) = 0 := fun k => by
        rw [ApnCipherC5.ddt_zero_row, if_neg hb]; simp
      simp [h, hb]
  · unfold ApnCipherC5.avgDP
    have h : ∀ k, ApnCipherC5.ddt (F k) a 0 = 0 := fun k => ApnCipherC5.ddt_to_zero (F k) (hF k) ha
    simp [h]

/-- BRIDGE (additive): the real key-averaged DP of the w = 2 superbox through an additive mixer M equals
K2A of the local averaged DDTs. -/
theorem avg_w2A_eq {κ1 κ2 κ3 κ4 : Type*} [Fintype κ1] [Nonempty κ1] [Fintype κ2] [Nonempty κ2]
    [Fintype κ3] [Nonempty κ3] [Fintype κ4] [Nonempty κ4]
    (F1 : κ1 → A → A) (F2 : κ2 → A → A) (g1 : κ3 → A ≃ A) (g2 : κ4 → A ≃ A)
    (M : (A × A) ≃+ (A × A)) (α γ : A × A) :
    ApnCipherC5.avgDP (ApnCipherC5.compK (parKA F1 F2) M (parEA g1 g2)) α γ =
      K2A (ApnCipherC5.avgDP F1) (ApnCipherC5.avgDP F2)
        (ApnCipherC5.avgDP (fun k => (g1 k : A → A))) (ApnCipherC5.avgDP (fun k => (g2 k : A → A)))
        M α γ := by
  rw [ApnCipherC5.avg_comp_eq, parEA_coe]
  simp_rw [avgDP_parKA]
  rw [Fintype.sum_prod_type]
  unfold K2A
  refine Finset.sum_congr rfl (fun d1 _ => Finset.sum_congr rfl (fun d2 _ => ?_))
  ring

/-- w = 2 split tail (2,2,1,1) through an additive MDS mixer: real key average ≤ ε². -/
theorem w2A_split_tail_le {κ1 κ2 κ3 κ4 κ5 κ6 : Type*} [Fintype κ1] [Nonempty κ1]
    [Fintype κ2] [Nonempty κ2] [Fintype κ3] [Nonempty κ3] [Fintype κ4] [Nonempty κ4]
    [Fintype κ5] [Nonempty κ5] [Fintype κ6] [Nonempty κ6]
    (F1 : κ1 → A → A) (F2 : κ2 → A → A) (g1 : κ3 → A ≃ A) (g2 : κ4 → A ≃ A)
    (hF1 : ∀ k, Function.Injective (F1 k)) (hF2 : ∀ k, Function.Injective (F2 k))
    (M : (A × A) ≃+ (A × A)) (hM : IsMDS2A M)
    (M2 M3 : (A × A) ≃+ (A × A)) (C3 : κ5 → (A × A) ≃ (A × A)) (C4 : κ6 → (A × A) ≃ (A × A))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hb1 : ∀ a b, a ≠ 0 → ApnCipherC5.avgDP F1 a b ≤ ε)
    (hb2 : ∀ a b, a ≠ 0 → ApnCipherC5.avgDP F2 a b ≤ ε)
    (hb3 : ∀ a b, a ≠ 0 → ApnCipherC5.avgDP (fun k => (g1 k : A → A)) a b ≤ ε)
    (hb4 : ∀ a b, a ≠ 0 → ApnCipherC5.avgDP (fun k => (g2 k : A → A)) a b ≤ ε)
    {α : A × A} (hα : α ≠ 0) (γ : A × A) :
    ApnCipherC5.avgDP (ApnCipherC5.compK (ApnCipherC5.compK
      (ApnCipherC5.compK (parKA F1 F2) M (parEA g1 g2)) M2 C3) M3 C4) α γ ≤ ε ^ 2 := by
  refine ApnCipherC5.four_layer_le _ M2 M3 C3 C4 α (ε ^ 2) (fun δ => ?_) γ
  rw [avg_w2A_eq]
  exact mds2A_le hε (isKerA_avg F1 hF1 hb1) (isKerA_avg F2 hF2 hb2)
    (isKerA_avg (fun k => (g1 k : A → A)) (fun k => (g1 k).injective) hb3)
    (isKerA_avg (fun k => (g2 k : A → A)) (fun k => (g2 k).injective) hb4)
    M hM hα δ

end MixAdd

end ApnCipherC9

end
