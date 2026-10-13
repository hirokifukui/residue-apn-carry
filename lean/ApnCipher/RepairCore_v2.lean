/-
P7-13 (C7, Claude 2026-10-12): ONE component -- the short abstract core of the repair theorem
(paper: c7 notes, general affine d; C6 H_CERT_P6 for d0).  Three blocks:
 (1) coeff_not_both_zero: if ℓ² = A² + B ≠ 0 then (A + βτ, B + β²τ²) are not both 0
     (the two top coefficients of Φ, up to the nonzero factors β^{s−1}, β^{s−2}).
 (2) nonzero_count_ge: a polynomial Φ ∈ F[C] with natDegree ≤ s, [C^s]Φ = 0 and
     [C^{s−1}]Φ ≠ 0 or [C^{s−2}]Φ ≠ 0 is nonzero at ≥ q − (s−1) points (= q/2 + 2 for s = q/2 − 1).
 (3) linear certificate on an ARBITRARY finite F-module V (the full space F^F or any subspace
     containing g, e.g. Boolean degree ≤ 2): if ℓ g = 1 then ℓ is surjective, ℓ(h + λg) = ℓ h + λ,
     exactly one λ fails, and q · #{ℓ = 0} = |V|, i.e. q · #{ℓ ≠ 0} + |V| = q · |V|
     (the pass fraction is exactly 1 − 1/q).
NOT here (paper, correspondence table in c7/notes/resp/P7-13.md): the identification of ℓ with
A_d + sqrt(B_d), the computation [C^k]Φ = Σ z^{s−k} d^k (Lucas), the power sums over H,
ℓ(g_d) = 1, Ψ = Φ², the Boolean-degree statements.
-/
import Mathlib
-- v2: build 1 of RepairCore.lean exit 1 (identifier λ' is a keyword); renamed to lam, nothing else changed

noncomputable section

open Finset Polynomial

namespace ApnCipherC7

section Coeff

variable {F : Type*} [Field F]

/-- (1) if A² + B ≠ 0 the two top coefficients do not vanish simultaneously (any characteristic). -/
theorem coeff_not_both_zero (A B β τ : F) (hℓ : A ^ 2 + B ≠ 0) :
    A + β * τ ≠ 0 ∨ B + β ^ 2 * τ ^ 2 ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hℓ
  have hA : A = -(β * τ) := by linear_combination h1
  rw [hA]
  linear_combination h2

end Coeff

section Roots

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- (2) the root-count core. -/
theorem nonzero_count_ge (Φ : F[X]) (s : ℕ) (hs2 : 2 ≤ s) (hdeg : Φ.natDegree ≤ s)
    (hs : Φ.coeff s = 0) (hc : Φ.coeff (s - 1) ≠ 0 ∨ Φ.coeff (s - 2) ≠ 0) :
    Fintype.card F - (s - 1) ≤ (univ.filter (fun c => Φ.eval c ≠ 0)).card := by
  have hΦ : Φ ≠ 0 := by
    intro h0; subst h0
    rcases hc with h | h <;> simp at h
  have hdeg' : Φ.natDegree ≤ s - 1 := by
    have hne : Φ.natDegree ≠ s := by
      intro heq
      apply hΦ
      have : Φ.leadingCoeff = 0 := by rw [leadingCoeff, heq]; exact hs
      exact leadingCoeff_eq_zero.mp this
    omega
  have hroots : (univ.filter (fun c => Φ.eval c = 0)).card ≤ s - 1 := by
    have hsub : univ.filter (fun c => Φ.eval c = 0) ⊆ Φ.roots.toFinset := by
      intro c hc'
      simp only [mem_filter, mem_univ, true_and] at hc'
      rw [Multiset.mem_toFinset, mem_roots hΦ]
      exact hc'
    calc _ ≤ Φ.roots.toFinset.card := card_le_card hsub
      _ ≤ Φ.roots.card := Multiset.toFinset_card_le _
      _ ≤ Φ.natDegree := card_roots' Φ
      _ ≤ s - 1 := hdeg'
  have hsplit := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset F))
    (fun c => Φ.eval c = 0)
  rw [card_univ] at hsplit
  have : (univ.filter (fun c => ¬ Φ.eval c = 0)).card
      = (univ.filter (fun c => Φ.eval c ≠ 0)).card := rfl
  omega

end Roots

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

end ApnCipherC7

end
