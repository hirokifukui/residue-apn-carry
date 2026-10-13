/-
P8-11 (C8, Claude 2026-10-12): ONE component -- the repair link on ACTUAL definitions.
F a finite field of characteristic 2 with |F| = q = 2^(n+1) (so q/2 = 2^n), a finite index set T ⊆ F
(paper: the transversal {a : χ a = 0} of the fibres {a, a+ρ} of r), r : F → F, ρ : F:
  Δ_h(a) = h a + h (a + ρ),
  A_d(h) = Σ_{a∈T} r(a)^{-3} Δ_h(a),   B_d(h) = Σ_{a∈T} r(a)^{-5} Δ_h(a)^2,
  ℓ_d(h) = A_d(h) + B_d(h)^(q/2)      -- ellD, an F-linear map (F → F) →ₗ[F] F, PROVED (Frobenius:
           (x+y)^(2^n) = x^(2^n) + y^(2^n), c^(2·2^n) = c^q = c).
  g_d = χ · r with χ(a+ρ) = χ(a) + 1, r(a+ρ) = r(a)  ⇒  Δ_{g_d} = r pointwise (Dlt_gd), and
  ℓ_d(g_d) = Σ_T r^{-2} + (Σ_T r^{-3})^(q/2) (ellD_gd; the power sums p₂ = 1, p₃ = 0 stay on paper).
The abstract certificate lemmas of C7 RepairCore_v2 (section Linear) are copied VERBATIM into namespace
ApnCipherC8 and applied to ℓ_d on V = (F → F): with ℓ_d(g_d) = 1 as the ONLY remaining hypothesis,
the repair rule, exactly one failure per line h + λ g_d, and the exact pass fraction 1 − 1/q hold.
NOT here: the power sums over H, Φ / Ψ and the Boolean-degree statements.
-/
import Mathlib
-- v2: build 1 of RepairLink.lean exit 1 (Dlt_gd: rw under an unreduced beta-redex); `simp only` instead, nothing else changed

noncomputable section

open Finset

namespace ApnCipherC8

section Linear

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]

/-- (3a) ℓ g = 1 ⇒ ℓ surjective. -/
theorem cert_surjective (ℓ : V →ₗ[F] F) (g : V) (hg : ℓ g = 1) : Function.Surjective ℓ :=
  fun t => ⟨t • g, by simp [hg]⟩

/-- (3b) the one-term repair rule. -/
theorem cert_repair (ℓ : V →ₗ[F] F) (g : V) (hg : ℓ g = 1) (h : V) (lam : F) :
    ℓ (h + lam • g) = ℓ h + lam := by
  simp [hg]

/-- (3c) for every h exactly one of the q choices h + λ g fails the certificate. -/
theorem cert_one_failure (ℓ : V →ₗ[F] F) (g : V) (hg : ℓ g = 1) (h : V) :
    (univ.filter (fun lam : F => ℓ (h + lam • g) = 0)).card = 1 := by
  rw [card_eq_one]
  refine ⟨-ℓ h, ?_⟩
  ext lam
  simp only [mem_filter, mem_univ, true_and, mem_singleton, cert_repair ℓ g hg]
  constructor
  · intro h0; linear_combination h0
  · intro h0; rw [h0]; ring

/-- (3d) every fibre of ℓ has the size of the kernel, hence q · #ker = |V|. -/
theorem cert_kernel_count (ℓ : V →ₗ[F] F) (g : V) (hg : ℓ g = 1) :
    Fintype.card F * (univ.filter (fun v => ℓ v = 0)).card = Fintype.card V := by
  classical
  have hfib : ∀ t : F, (univ.filter (fun v => ℓ v = t)).card
      = (univ.filter (fun v => ℓ v = 0)).card := by
    intro t
    refine Finset.card_nbij' (fun v => v - t • g) (fun v => v + t • g) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
      simp [hg, hv]
    · intro v hv
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
      simp [hg, hv]
    · intro v _; simp
    · intro v _; simp
  have hsum := card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset F))
    (f := fun v => ℓ v) (fun v _ => mem_univ _)
  rw [card_univ] at hsum
  rw [hsum]
  simp_rw [hfib]
  rw [sum_const, card_univ, smul_eq_mul]

/-- (3e) exact pass fraction 1 − 1/q:  q · #{ℓ ≠ 0} + |V| = q · |V|. -/
theorem cert_pass_count (ℓ : V →ₗ[F] F) (g : V) (hg : ℓ g = 1) :
    Fintype.card F * (univ.filter (fun v => ℓ v ≠ 0)).card + Fintype.card V
      = Fintype.card F * Fintype.card V := by
  have h0 := cert_kernel_count ℓ g hg
  have hsplit := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V))
    (fun v => ℓ v = 0)
  rw [card_univ] at hsplit
  have : (univ.filter (fun v => ¬ ℓ v = 0)).card = (univ.filter (fun v => ℓ v ≠ 0)).card := rfl
  rw [← this]
  calc Fintype.card F * (univ.filter (fun v => ¬ ℓ v = 0)).card + Fintype.card V
      = Fintype.card F * (univ.filter (fun v => ¬ ℓ v = 0)).card
          + Fintype.card F * (univ.filter (fun v => ℓ v = 0)).card := by rw [h0]
    _ = Fintype.card F * ((univ.filter (fun v => ℓ v = 0)).card
          + (univ.filter (fun v => ¬ ℓ v = 0)).card) := by ring
    _ = Fintype.card F * Fintype.card V := by rw [hsplit]

end Linear

section RepairLink

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Δ_h(a) = h(a) + h(a + ρ). -/
def Dlt (ρ : F) (h : F → F) (a : F) : F := h a + h (a + ρ)

/-- A_d(h). -/
def Ad (T : Finset F) (r : F → F) (ρ : F) (h : F → F) : F :=
  ∑ a ∈ T, (r a)⁻¹ ^ 3 * Dlt ρ h a

/-- B_d(h). -/
def Bd (T : Finset F) (r : F → F) (ρ : F) (h : F → F) : F :=
  ∑ a ∈ T, (r a)⁻¹ ^ 5 * Dlt ρ h a ^ 2

omit [Fintype F] [DecidableEq F] in
theorem two_eq_zero_char2 : (2 : F) = 0 := by
  have := CharP.cast_eq_zero F 2
  exact_mod_cast this

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem Ad_add (T : Finset F) (r : F → F) (ρ : F) (h h' : F → F) :
    Ad T r ρ (h + h') = Ad T r ρ h + Ad T r ρ h' := by
  unfold Ad Dlt
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun a _ => ?_)
  simp only [Pi.add_apply]
  ring

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem Ad_smul (T : Finset F) (r : F → F) (ρ : F) (c : F) (h : F → F) :
    Ad T r ρ (c • h) = c * Ad T r ρ h := by
  unfold Ad Dlt
  rw [mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype F] [DecidableEq F] in
theorem Bd_add (T : Finset F) (r : F → F) (ρ : F) (h h' : F → F) :
    Bd T r ρ (h + h') = Bd T r ρ h + Bd T r ρ h' := by
  have h2 : (2 : F) = 0 := two_eq_zero_char2
  unfold Bd Dlt
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun a _ => ?_)
  simp only [Pi.add_apply]
  linear_combination ((r a)⁻¹ ^ 5 * (h a + h (a + ρ)) * (h' a + h' (a + ρ))) * h2

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem Bd_smul (T : Finset F) (r : F → F) (ρ : F) (c : F) (h : F → F) :
    Bd T r ρ (c • h) = c ^ 2 * Bd T r ρ h := by
  unfold Bd Dlt
  rw [mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- ℓ_d(h) = A_d(h) + B_d(h)^(q/2), with q = 2^(n+1): an F-linear functional on F^F. -/
def ellD (n : ℕ) (hcard : Fintype.card F = 2 ^ (n + 1)) (T : Finset F) (r : F → F) (ρ : F) :
    (F → F) →ₗ[F] F where
  toFun h := Ad T r ρ h + Bd T r ρ h ^ (2 ^ n)
  map_add' h h' := by
    rw [Ad_add, Bd_add, add_pow_char_pow]
    ring
  map_smul' c h := by
    rw [Ad_smul, Bd_smul, mul_pow, ← pow_mul]
    have hc : c ^ (2 * 2 ^ n) = c := by
      rw [show 2 * 2 ^ n = Fintype.card F by rw [hcard, pow_succ]; ring]
      exact FiniteField.pow_card c
    rw [hc, RingHom.id_apply, smul_eq_mul]
    ring

theorem ellD_apply (n : ℕ) (hcard : Fintype.card F = 2 ^ (n + 1)) (T : Finset F) (r : F → F)
    (ρ : F) (h : F → F) :
    ellD n hcard T r ρ h = Ad T r ρ h + Bd T r ρ h ^ (2 ^ n) := rfl

omit [Fintype F] [DecidableEq F] in
/-- Δ_{g_d} = r pointwise for g_d = χ · r, χ(a+ρ) = χ(a) + 1, r(a+ρ) = r(a). -/
theorem Dlt_gd (χ r : F → F) (ρ : F) (hχ : ∀ a, χ (a + ρ) = χ a + 1)
    (hr : ∀ a, r (a + ρ) = r a) (a : F) :
    Dlt ρ (fun a => χ a * r a) a = r a := by
  have h2 : (2 : F) = 0 := two_eq_zero_char2
  unfold Dlt
  simp only [hχ, hr]
  linear_combination (χ a * r a) * h2

/-- ℓ_d(g_d) reduces to the two reciprocal power sums over T (their values stay on paper). -/
theorem ellD_gd (n : ℕ) (hcard : Fintype.card F = 2 ^ (n + 1)) (T : Finset F) (χ r : F → F)
    (ρ : F) (hχ : ∀ a, χ (a + ρ) = χ a + 1) (hr : ∀ a, r (a + ρ) = r a) :
    ellD n hcard T r ρ (fun a => χ a * r a)
      = ∑ a ∈ T, (r a)⁻¹ ^ 3 * r a + (∑ a ∈ T, (r a)⁻¹ ^ 5 * r a ^ 2) ^ (2 ^ n) := by
  rw [ellD_apply]
  unfold Ad Bd
  simp only [Dlt_gd χ r ρ hχ hr]

/-- repair rule for the actual ℓ_d. -/
theorem ellD_repair (n : ℕ) (hcard : Fintype.card F = 2 ^ (n + 1)) (T : Finset F) (χ r : F → F)
    (ρ : F) (hg : ellD n hcard T r ρ (fun a => χ a * r a) = 1) (h : F → F) (lam : F) :
    ellD n hcard T r ρ (h + lam • (fun a => χ a * r a)) = ellD n hcard T r ρ h + lam :=
  cert_repair _ _ hg h lam

/-- exactly one failure on every line h + λ g_d. -/
theorem ellD_one_failure (n : ℕ) (hcard : Fintype.card F = 2 ^ (n + 1)) (T : Finset F)
    (χ r : F → F) (ρ : F) (hg : ellD n hcard T r ρ (fun a => χ a * r a) = 1) (h : F → F) :
    (univ.filter (fun lam : F => ellD n hcard T r ρ (h + lam • (fun a => χ a * r a)) = 0)).card
      = 1 :=
  cert_one_failure _ _ hg h

/-- exact pass fraction 1 − 1/q of the actual certificate on V = F^F. -/
theorem ellD_pass_count (n : ℕ) (hcard : Fintype.card F = 2 ^ (n + 1)) (T : Finset F)
    (χ r : F → F) (ρ : F) (hg : ellD n hcard T r ρ (fun a => χ a * r a) = 1) :
    Fintype.card F * (univ.filter (fun h : F → F => ellD n hcard T r ρ h ≠ 0)).card
        + Fintype.card (F → F)
      = Fintype.card F * Fintype.card (F → F) :=
  cert_pass_count _ _ hg

end RepairLink

end ApnCipherC8

end
