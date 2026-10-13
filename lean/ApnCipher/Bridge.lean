/-
P8-09 (b) (C8, Claude 2026-10-12): ONE component -- the bridge from the actual local key family on a
carry-coordinatised group G to the two-step bound, and the instantiation of C5 W2Bridge.
  * B_G := φ⁻¹ ∘ pdB ∘ φ, F_G := φ⁻¹ ∘ pdF ∘ φ (as permutations of G; p injective, d nowhere 0);
  * S2 k  x = F_G(B_G(B_G(x) + k₁) + k₂)            (keys k = (k₁, k₂), paper's S_2),
    S2w k x = S2 (k₁,k₂) (x + k₀)                    (with the whitening key k₀; keys independent, uniform);
  * avgDP_S2w_eq : whitening does not change the averaged DP;
  * avgDP_S2_eq  : avgDP S2 = Σ_δ (Σ_δ₁ T_B(a,δ₁) T_B(δ₁,δ)) T_F(δ,γ)   (C5 avg_comp_eq twice, M = refl),
                   T = ddt/|G| of B_G, F_G (exact, no inequality);
  * avgDP_S2_le  : a ≠ 0 ⇒ avgDP S2 a γ ≤ 4/|G|  (TwoStep.two_step_pd with π = first row of T_B,
                   whose warm-start properties are proved here from OneRound.dp_pdB_le, rowsum_le, ddtC_to_zero);
  * w2_pd_le     : C5 w2_split_tail_le with F1 = F2 = S2w, g1 = g2 = S2, ε = 4/|G|; hb1–hb4 discharged.
Remaining hypotheses: hφ (φ carries + to cadd (star e)), PD (p injective + APN, ker K = {0, ρ}, ε + K a ≠ 0),
ρ = e.symm (Pi.single i 1) (weight one), 12 ≤ q, and the C5 structural hypotheses (mixer entries/determinant
units, M2 M3 additive, C3 C4 permutations).
-/
import ApnCipher.TwoStep
import ApnCipher.Transport_v2
import ApnCipher.W2Bridge

noncomputable section

open Finset

namespace ApnCipherC8

open ApnCipherC7

section Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def pdBequiv (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    (F × F) ≃ (F × F) :=
  Equiv.ofBijective (pdB p h d) (pdB_injective p h d hp hd0).bijective_of_finite

def pdFequiv (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    (F × F) ≃ (F × F) :=
  Equiv.ofBijective (pdF p h d) (pdF_injective p h d hp hd0).bijective_of_finite

/-- B on G (conjugate by the coordinate map φ). -/
def Bg (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    G ≃ G :=
  (φ.trans (pdBequiv p h d hp hd0)).trans φ.symm

/-- F on G. -/
def Fg (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    G ≃ G :=
  (φ.trans (pdFequiv p h d hp hd0)).trans φ.symm

/-- the local block S_2 with keys (k₁, k₂). -/
def S2 (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    G × G → G ≃ G := fun k =>
  ((Bg φ p h d hp hd0).trans (Equiv.addRight k.1)).trans
    ((Bg φ p h d hp hd0).trans ((Equiv.addRight k.2).trans (Fg φ p h d hp hd0)))

theorem S2_apply (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p)
    (hd0 : ∀ a, d a ≠ 0) (k : G × G) (x : G) :
    S2 φ p h d hp hd0 k x
      = Fg φ p h d hp hd0 (Bg φ p h d hp hd0 (Bg φ p h d hp hd0 x + k.1) + k.2) := rfl

/-- the local block with whitening key k₀: S_2(x + k₀; k₁, k₂). -/
def S2w (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    G × G × G → G → G := fun k x => S2 φ p h d hp hd0 k.2 (x + k.1)

theorem S2w_apply (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p)
    (hd0 : ∀ a, d a ≠ 0) (k : G × G × G) (x : G) :
    S2w φ p h d hp hd0 k x
      = Fg φ p h d hp hd0 (Bg φ p h d hp hd0 (Bg φ p h d hp hd0 (x + k.1) + k.2.1) + k.2.2) := rfl

theorem Bg_conj (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p)
    (hd0 : ∀ a, d a ≠ 0) : (fun z => φ (Bg φ p h d hp hd0 (φ.symm z))) = pdB p h d := by
  funext z
  simp [Bg, pdBequiv]

theorem Fg_conj (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p)
    (hd0 : ∀ a, d a ≠ 0) : (fun z => φ (Fg φ p h d hp hd0 (φ.symm z))) = pdF p h d := by
  funext z
  simp [Fg, pdFequiv]

/-- translation invariance of the DDT. -/
theorem ddt_addRight (f : G → G) (k a b : G) :
    ApnCipherC5.ddt (fun x => f (x + k)) a b = ApnCipherC5.ddt f a b := by
  unfold ApnCipherC5.ddt
  refine Finset.card_nbij' (fun x => x + k) (fun y => y - k) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_coe, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [add_right_comm]; exact hx
  · intro y hy
    simp only [coe_filter, mem_coe, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
    have h1 : y - k + a + k = y + a := by abel
    rw [h1, sub_add_cancel]; exact hy
  · intro x _; simp
  · intro y _; simp

/-- reindexing the key space by an equivalence does not change avgDP. -/
theorem avgDP_reindex {κ κ' : Type*} [Fintype κ] [Fintype κ'] (E : κ → G → G) (E' : κ' → G → G)
    (σ : κ ≃ κ') (hE : ∀ k, E k = E' (σ k)) (a b : G) :
    ApnCipherC5.avgDP E a b = ApnCipherC5.avgDP E' a b := by
  unfold ApnCipherC5.avgDP
  rw [Fintype.card_congr σ]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun k => by simp only [hE k])

/-- a one-element key space: avgDP is the normalised DDT. -/
theorem avgDP_unit (f : G → G) (a b : G) :
    ApnCipherC5.avgDP (fun _ : Unit => f) a b = (ApnCipherC5.ddt f a b : ℝ) / Fintype.card G := by
  unfold ApnCipherC5.avgDP
  simp

/-- the whitening key does not change the averaged DP. -/
theorem avgDP_S2w_eq (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p)
    (hd0 : ∀ a, d a ≠ 0) (a γ : G) :
    ApnCipherC5.avgDP (S2w φ p h d hp hd0) a γ
      = ApnCipherC5.avgDP (fun k => (S2 φ p h d hp hd0 k : G → G)) a γ := by
  have hG0 : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold ApnCipherC5.avgDP
  rw [Fintype.sum_prod_type (fun k : G × G × G => (ApnCipherC5.ddt (S2w φ p h d hp hd0 k) a γ : ℝ))]
  have h1 : ∀ (k0 : G) (k' : G × G), (ApnCipherC5.ddt (S2w φ p h d hp hd0 (k0, k')) a γ : ℝ)
      = ApnCipherC5.ddt (S2 φ p h d hp hd0 k') a γ := fun k0 k' =>
    congrArg (Nat.cast : ℕ → ℝ) (ddt_addRight (S2 φ p h d hp hd0 k') k0 a γ)
  simp_rw [h1]
  rw [sum_const, card_univ, nsmul_eq_mul]
  rw [show (Fintype.card (G × G × G) : ℝ) = Fintype.card G * Fintype.card (G × G) by
    rw [Fintype.card_prod, Nat.cast_mul]]
  rw [mul_assoc, mul_div_mul_left _ _ hG0]

/-- exact kernel composition for S2 (C5 avg_comp_eq twice, mixer = identity). -/
theorem avgDP_S2_eq (φ : G ≃ F × F) (p h d : F → F) (hp : Function.Injective p)
    (hd0 : ∀ a, d a ≠ 0) (a γ : G) :
    ApnCipherC5.avgDP (fun k => (S2 φ p h d hp hd0 k : G → G)) a γ
      = ∑ δ, (∑ δ₁, ((ApnCipherC5.ddt (Bg φ p h d hp hd0) a δ₁ : ℝ) / Fintype.card G)
              * ((ApnCipherC5.ddt (Bg φ p h d hp hd0) δ₁ δ : ℝ) / Fintype.card G))
            * ((ApnCipherC5.ddt (Fg φ p h d hp hd0) δ γ : ℝ) / Fintype.card G) := by
  let σ : G × G ≃ (Unit × Unit × G) × Unit × G :=
    { toFun := fun k => (((), (), k.1), (), k.2)
      invFun := fun z => (z.1.2.2, z.2.2)
      left_inv := fun k => rfl
      right_inv := fun z => rfl }
  rw [avgDP_reindex (fun k => (S2 φ p h d hp hd0 k : G → G))
    (ApnCipherC5.compK
      (ApnCipherC5.compK (fun _ : Unit => (Bg φ p h d hp hd0 : G → G)) (AddEquiv.refl G)
        (fun _ : Unit => Bg φ p h d hp hd0))
      (AddEquiv.refl G) (fun _ : Unit => Fg φ p h d hp hd0)) σ (fun k => rfl)]
  rw [ApnCipherC5.avg_comp_eq]
  simp_rw [ApnCipherC5.avg_comp_eq]
  simp only [avgDP_unit, AddEquiv.refl_apply]

theorem ddt_Bg {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (φ : G ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd (ApnCipherC7.star e) (φ x) (φ y))
    (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) (α β : G) :
    ApnCipherC5.ddt (Bg φ p h d hp hd0) α β = ddtC (ApnCipherC7.star e) (pdB p h d) (φ α) (φ β) := by
  have h1 := ApnCipherC7.ddt_eq_ddtC (ApnCipherC7.star e) φ hφ (Bg φ p h d hp hd0) α β
  rw [Bg_conj] at h1
  exact h1

theorem ddt_Fg {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (φ : G ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd (ApnCipherC7.star e) (φ x) (φ y))
    (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) (α β : G) :
    ApnCipherC5.ddt (Fg φ p h d hp hd0) α β = ddtC (ApnCipherC7.star e) (pdF p h d) (φ α) (φ β) := by
  have h1 := ApnCipherC7.ddt_eq_ddtC (ApnCipherC7.star e) φ hφ (Fg φ p h d hp hd0) α β
  rw [Fg_conj] at h1
  exact h1

/-- the two-block local bound on G: avgDP S2 ≤ 4/N for every nonzero input difference. -/
theorem avgDP_S2_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (φ : G ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd (ApnCipherC7.star e) (φ x) (φ y))
    (p h : F → F) (K : F →+ F) (ε : F) (i : Fin m)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = e.symm (Pi.single i 1))) (hε : ∀ a, ε + K a ≠ 0)
    (hp : Function.Injective p)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (hq : 12 ≤ (Fintype.card F : ℝ)) (a γ : G) (ha : a ≠ 0) :
    ApnCipherC5.avgDP (fun k => (S2 φ p h (fun a => ε + K a) hp hε k : G → G)) a γ
      ≤ 4 / (Fintype.card G : ℝ) := by
  have hcardG : (Fintype.card G : ℝ) = (Fintype.card F : ℝ) * Fintype.card F := by
    have := Fintype.card_congr φ
    rw [Fintype.card_prod] at this
    exact_mod_cast this
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) * Fintype.card F := by positivity
  have hρ : e.symm (Pi.single i (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have h1 := congrArg e h0
    rw [AddEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 i
    simp at h2
  have hφ0 : φ 0 = 0 := by
    have h00 := hφ 0 0
    simp only [add_zero, cadd] at h00
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
  rw [avgDP_S2_eq]
  simp_rw [ddt_Bg e φ hφ, ddt_Fg e φ hφ]
  rw [hcardG]
  -- reindex the two sums over G by φ
  have hin : ∀ δ : G, (∑ δ₁ : G,
      ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) (φ δ₁) : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F))
      * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ δ₁) (φ δ) : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F)))
      = ∑ z : F × F,
      ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F))
      * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) z (φ δ) : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F)) := fun δ =>
    Equiv.sum_comp φ (fun z =>
      ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F))
      * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) z (φ δ) : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F)))
  simp_rw [hin]
  -- the warm start π = first row of T_B
  have hπ0 : ∀ z, 0 ≤ (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
      / ((Fintype.card F : ℝ) * Fintype.card F) := fun z => by positivity
  have hπs : ∑ z, (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
      / ((Fintype.card F : ℝ) * Fintype.card F) ≤ 1 := by
    rw [← sum_div, div_le_one hN]
    have h1 := rowsum_le (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a)
    rw [Fintype.card_prod] at h1
    exact_mod_cast h1
  have hπz : (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) 0 : ℝ)
      / ((Fintype.card F : ℝ) * Fintype.card F) = 0 := by
    rw [ddtC_to_zero (ApnCipherC7.star e) (star_zero_right e) _
      (pdB_injective p h _ hp hε) (φ a) hφa]
    simp
  have hπx : ∀ z, (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
      / ((Fintype.card F : ℝ) * Fintype.card F) ≤ 1 / (Fintype.card F : ℝ) := by
    intro z
    have h1 := dp_pdB_le e p h K ε (e.symm (Pi.single i 1)) hρ hker hε hapn (φ a) hφa z
    rw [Fintype.card_prod, Nat.cast_mul] at h1
    exact h1
  have key := two_step_pd e p h K ε i hker hε hp hapn hq
    (fun z => (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
      / ((Fintype.card F : ℝ) * Fintype.card F)) hπ0 hπs hπz hπx (φ γ)
  refine le_trans (le_of_eq ?_) key
  exact Equiv.sum_comp φ (fun w => (∑ z : F × F,
      ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) (φ a) z : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F))
      * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) z w : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F)))
      * ((ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) w (φ γ) : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F)))

end Bridge

section W2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- C5 w2_split_tail_le with the actual local blocks: hb1–hb4 are theorems. -/
theorem w2_pd_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (φ : R ≃ F × F)
    (hφ : ∀ x y, φ (x + y) = cadd (ApnCipherC7.star e) (φ x) (φ y))
    (p h : F → F) (K : F →+ F) (ε : F) (i : Fin m)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = e.symm (Pi.single i 1))) (hε : ∀ a, ε + K a ≠ 0)
    (hp : Function.Injective p)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (hq : 12 ≤ (Fintype.card F : ℝ))
    {m11 m12 m21 m22 : R} (h11 : IsUnit m11) (h12 : IsUnit m12) (h21 : IsUnit m21)
    (h22 : IsUnit m22) (hdet : IsUnit (m11 * m22 - m12 * m21))
    {κ5 κ6 : Type*} [Fintype κ5] [Nonempty κ5] [Fintype κ6] [Nonempty κ6]
    (M2 M3 : (R × R) ≃+ (R × R)) (C3 : κ5 → (R × R) ≃ (R × R)) (C4 : κ6 → (R × R) ≃ (R × R))
    {α : R × R} (hα : α ≠ 0) (γ : R × R) :
    ApnCipherC5.avgDP
      (ApnCipherC5.compK (ApnCipherC5.compK (ApnCipherC5.compK
        (ApnCipherC5.parK (S2w φ p h (fun a => ε + K a) hp hε) (S2w φ p h (fun a => ε + K a) hp hε))
        (ApnCipherC5.mix2 m11 m12 m21 m22 hdet)
        (ApnCipherC5.parE (S2 φ p h (fun a => ε + K a) hp hε) (S2 φ p h (fun a => ε + K a) hp hε)))
        M2 C3) M3 C4) α γ
      ≤ (4 / (Fintype.card R : ℝ)) ^ 2 := by
  have hinj : ∀ k, Function.Injective (S2w φ p h (fun a => ε + K a) hp hε k) := by
    intro k x y hxy
    have h1 : x + k.1 = y + k.1 := (S2 φ p h (fun a => ε + K a) hp hε k.2).injective hxy
    exact add_right_cancel h1
  have hb : ∀ a b : R, a ≠ 0 →
      ApnCipherC5.avgDP (S2w φ p h (fun a => ε + K a) hp hε) a b ≤ 4 / (Fintype.card R : ℝ) := by
    intro a b ha
    rw [avgDP_S2w_eq]
    exact avgDP_S2_le e φ hφ p h K ε i hker hε hp hapn hq a b ha
  have hb' : ∀ a b : R, a ≠ 0 →
      ApnCipherC5.avgDP (fun k => (S2 φ p h (fun a => ε + K a) hp hε k : R → R)) a b
        ≤ 4 / (Fintype.card R : ℝ) :=
    fun a b ha => avgDP_S2_le e φ hφ p h K ε i hker hε hp hapn hq a b ha
  exact ApnCipherC5.w2_split_tail_le _ _ _ _ hinj hinj h11 h12 h21 h22 hdet M2 M3 C3 C4
    (by positivity) hb hb hb' hb' hα γ

end W2

end ApnCipherC8

end
