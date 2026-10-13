/-
P8-09 (a) (C8, Claude 2026-10-12): ONE component -- Theorem S (sup-norm recursion), one step started
from the warm start π = π₁ (every entry ≤ 1/q, OneRound), followed by the final layer F:
  Σ_β (π T_B)(β) · T_F(β, γ) ≤ 4/N      (ρ of weight one, q ≥ 12; the paper states q ≥ 32).
Two layers:
  * two_step_abstract : pure real arithmetic on arbitrary nonnegative "tables" tB, tF (counts) whose
    class column sums / entries satisfy exactly the hypotheses of the paper's Prop. table
    (SHyp: hZZ hZE hEZ hEE hGZ hGE hrow;  FHyp: hF0 hFZ hFZ' hFE hFG).  Conclusion in counts:
    Σ_β (Σ_α π α · tB α β) · tF β γ ≤ 4 · q².  (x = 1/q enters only through π ≤ x, x·q = 1.)
    The arithmetic is that of C3 WarmStart.edp2_of_init with ω = 2, done directly:
    σ_Z ≤ (2 + 2qx)/N = 4/N,  σ_E ≤ (q x q/2 + 2qx + 4)/N = (q/2 + 6)/N,
    final ≤ max(4, 2q·(q/2+6)/q² ·q² ... ) : 3q² + 12q ≤ 4q².
  * two_step_pd : the hypotheses discharged by ColsB_v3 / ColsF for the concrete PD layer on
    (F × F, cadd (star e)), ρ = e.symm (Pi.single i 1), normalised by N = q²:
    Σ_β (Σ_α π α · T_B(α,β)) · T_F(β,γ) ≤ 4 / q².
Remaining hypotheses of two_step_pd: PD (p injective + APN, K additive with ker K = {0, ρ}, ε + K a ≠ 0),
ρ of weight one (by construction), 12 ≤ q, and the warm-start properties of π (nonneg, Σ ≤ 1, π 0 = 0,
π ≤ 1/q).  In the bridge (Bridge.lean) π is the actual first-round row T_B(α, ·).
-/
import ApnCipher.ColsF_v2

noncomputable section

open Finset

namespace ApnCipherC8

open ApnCipherC7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
/-- split a sum over the first digit into the two special values z, ρ and the rest. -/
theorem sum_le_split (f g : F → ℝ) (z ρ : F) (hzρ : z ≠ ρ) (A B c : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hg : ∀ u, 0 ≤ g u) (hz : f z ≤ A) (hρ : f ρ ≤ B)
    (hother : ∀ u, u ≠ z → u ≠ ρ → f u ≤ c * g u) :
    ∑ u, f u ≤ A + B + c * ∑ u, g u := by
  have hpt : ∀ u, f u ≤ (if u = z then A else 0) + (if u = ρ then B else 0) + c * g u := by
    intro u
    have hcg : 0 ≤ c * g u := mul_nonneg hc (hg u)
    by_cases h1 : u = z
    · subst h1
      rw [if_pos rfl, if_neg hzρ]
      linarith
    · by_cases h2 : u = ρ
      · subst h2
        rw [if_neg h1, if_pos rfl]
        linarith
      · rw [if_neg h1, if_neg h2]
        linarith [hother u h1 h2]
  calc ∑ u, f u ≤ ∑ u, ((if u = z then A else 0) + (if u = ρ then B else 0) + c * g u) :=
        sum_le_sum (fun u _ => hpt u)
    _ = A + B + c * ∑ u, g u := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
        simp

omit [Field F] [DecidableEq F] in
theorem wsum_le (w c : F → ℝ) (y : ℝ) (hwy : ∀ v, w v ≤ y) (hc : ∀ v, 0 ≤ c v) :
    ∑ v, w v * c v ≤ y * ∑ v, c v := by
  rw [mul_sum]
  exact sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (hwy v) (hc v))

omit [Field F] [DecidableEq F] in
theorem wsum_le' (w c : F → ℝ) (y : ℝ) (hw0 : ∀ v, 0 ≤ w v) (hcy : ∀ v, c v ≤ y) :
    ∑ v, w v * c v ≤ y * ∑ v, w v := by
  rw [mul_sum]
  exact sum_le_sum (fun v _ => by rw [mul_comm y]; exact mul_le_mul_of_nonneg_left (hcy v) (hw0 v))

/-- Theorem S, one step from the warm start, then the final layer: abstract arithmetic. -/
theorem two_step_abstract (tB tF : F × F → F × F → ℝ) (π : F × F → ℝ) (ρ : F) (hρ : ρ ≠ 0)
    (q x : ℝ) (hq : 12 ≤ q) (hx0 : 0 ≤ x) (hxq : x * q = 1)
    (htB0 : ∀ α β, 0 ≤ tB α β) (htF0 : ∀ α β, 0 ≤ tF α β)
    (hZZ : ∀ v t : F, v ≠ 0 → tB (0, v) (0, t) = 0)
    (hZE : ∀ t : F, ∑ v, tB (0, v) (ρ, t) ≤ q * q / 2)
    (hEZ : ∀ t : F, ∑ v, tB (ρ, v) (0, t) ≤ 2 * q)
    (hEE : ∀ t : F, ∑ v, tB (ρ, v) (ρ, t) ≤ 2 * q)
    (hGZ : ∀ u v t : F, u ≠ 0 → u ≠ ρ → tB (u, v) (0, t) ≤ 2)
    (hGE : ∀ u v t : F, u ≠ 0 → u ≠ ρ → tB (u, v) (ρ, t) ≤ 4)
    (hrow : ∀ α, ∑ β, tB α β ≤ q * q)
    (hF0 : ∀ (u v : F) (γ : F × F), u ≠ 0 → γ.1 = 0 → tF (u, v) γ = 0)
    (hFZ : ∀ γ : F × F, ∑ v, tF (0, v) γ ≤ q * q)
    (hFZ' : ∀ (v : F) (γ : F × F), γ.1 ≠ 0 → tF (0, v) γ = 0)
    (hFE : ∀ γ : F × F, ∑ v, tF (ρ, v) γ ≤ 2 * q)
    (hFG : ∀ (u v : F) (γ : F × F), u ≠ 0 → u ≠ ρ → tF (u, v) γ ≤ 2)
    (hπ0 : ∀ α, 0 ≤ π α) (hπs : ∑ α, π α ≤ 1) (hπz : π 0 = 0) (hπx : ∀ α, π α ≤ x)
    (γ : F × F) :
    ∑ β, (∑ α, π α * tB α β) * tF β γ ≤ 4 * (q * q) := by
  have hq0 : 0 < q := by linarith
  have h0ρ : (0 : F) ≠ ρ := fun h => hρ h.symm
  have hπuv : ∑ u, ∑ v, π (u, v) ≤ 1 := by
    calc ∑ u, ∑ v, π (u, v) = ∑ α, π α := (Fintype.sum_prod_type π).symm
      _ ≤ 1 := hπs
  have hgπ : ∀ u, 0 ≤ ∑ v, π (u, v) := fun u => sum_nonneg (fun v _ => hπ0 _)
  have hπ00 : π ((0 : F), (0 : F)) = 0 := hπz
  -- σ_Z: every Z (and zero) target receives ≤ 4 (= 4/N after normalisation)
  have hSZ : ∀ t : F, ∑ α, π α * tB α (0, t) ≤ 4 := by
    intro t
    rw [Fintype.sum_prod_type]
    have hsplit := sum_le_split (fun u => ∑ v, π (u, v) * tB (u, v) (0, t))
      (fun u => ∑ v, π (u, v)) 0 ρ h0ρ 0 2 2 le_rfl (by norm_num) (by norm_num) hgπ
      (by
        apply le_of_eq
        refine sum_eq_zero (fun v _ => ?_)
        by_cases hv : v = 0
        · rw [hv, hπ00, zero_mul]
        · rw [hZZ v t hv, mul_zero])
      (by
        calc ∑ v, π (ρ, v) * tB (ρ, v) (0, t) ≤ x * ∑ v, tB (ρ, v) (0, t) :=
              wsum_le _ _ x (fun v => hπx _) (fun v => htB0 _ _)
          _ ≤ x * (2 * q) := mul_le_mul_of_nonneg_left (hEZ t) hx0
          _ = 2 := by linear_combination 2 * hxq)
      (fun u hu0 huρ => wsum_le' _ _ 2 (fun v => hπ0 _) (fun v => hGZ u v t hu0 huρ))
    try beta_reduce at hsplit
    linarith
  -- σ_E: every E target receives ≤ q/2 + 6
  have hSE : ∀ t : F, ∑ α, π α * tB α (ρ, t) ≤ q / 2 + 6 := by
    intro t
    rw [Fintype.sum_prod_type]
    have hsplit := sum_le_split (fun u => ∑ v, π (u, v) * tB (u, v) (ρ, t))
      (fun u => ∑ v, π (u, v)) 0 ρ h0ρ (q / 2) 2 4 (by linarith) (by norm_num) (by norm_num) hgπ
      (by
        calc ∑ v, π (0, v) * tB (0, v) (ρ, t) ≤ x * ∑ v, tB (0, v) (ρ, t) :=
              wsum_le _ _ x (fun v => hπx _) (fun v => htB0 _ _)
          _ ≤ x * (q * q / 2) := mul_le_mul_of_nonneg_left (hZE t) hx0
          _ = q / 2 := by linear_combination (q / 2) * hxq)
      (by
        calc ∑ v, π (ρ, v) * tB (ρ, v) (ρ, t) ≤ x * ∑ v, tB (ρ, v) (ρ, t) :=
              wsum_le _ _ x (fun v => hπx _) (fun v => htB0 _ _)
          _ ≤ x * (2 * q) := mul_le_mul_of_nonneg_left (hEE t) hx0
          _ = 2 := by linear_combination 2 * hxq)
      (fun u hu0 huρ => wsum_le' _ _ 4 (fun v => hπ0 _) (fun v => hGE u v t hu0 huρ))
    try beta_reduce at hsplit
    linarith
  -- π₂ is nonnegative with total ≤ N
  have hπ2nn : ∀ β, 0 ≤ ∑ α, π α * tB α β :=
    fun β => sum_nonneg (fun α _ => mul_nonneg (hπ0 α) (htB0 α β))
  have hπ2s : ∑ β, ∑ α, π α * tB α β ≤ q * q := by
    rw [sum_comm]
    calc ∑ α, ∑ β, π α * tB α β = ∑ α, π α * ∑ β, tB α β := by
          refine sum_congr rfl (fun α _ => ?_); rw [mul_sum]
      _ ≤ ∑ α, π α * (q * q) :=
          sum_le_sum (fun α _ => mul_le_mul_of_nonneg_left (hrow α) (hπ0 α))
      _ = (q * q) * ∑ α, π α := by rw [mul_sum]; refine sum_congr rfl (fun α _ => by ring)
      _ ≤ (q * q) * 1 := mul_le_mul_of_nonneg_left hπs (by positivity)
      _ = q * q := mul_one _
  -- final layer
  rw [Fintype.sum_prod_type]
  by_cases hγ : γ.1 = 0
  · rw [sum_eq_single (0 : F)]
    · calc ∑ w, (∑ α, π α * tB α (0, w)) * tF (0, w) γ ≤ 4 * ∑ w, tF (0, w) γ :=
            wsum_le _ _ 4 (fun w => hSZ w) (fun w => htF0 _ _)
        _ ≤ 4 * (q * q) := mul_le_mul_of_nonneg_left (hFZ γ) (by norm_num)
    · intro s _ hs
      refine sum_eq_zero (fun w _ => ?_)
      rw [hF0 s w γ hs hγ, mul_zero]
    · intro h; exact absurd (mem_univ _) h
  · have hsplit := sum_le_split (fun s => ∑ w, (∑ α, π α * tB α (s, w)) * tF (s, w) γ)
      (fun s => ∑ w, ∑ α, π α * tB α (s, w)) 0 ρ h0ρ 0 ((q / 2 + 6) * (2 * q)) 2 le_rfl
      (by positivity) (by norm_num) (fun s => sum_nonneg (fun w _ => hπ2nn _))
      (by
        apply le_of_eq
        refine sum_eq_zero (fun w _ => ?_)
        rw [hFZ' w γ hγ, mul_zero])
      (by
        calc ∑ w, (∑ α, π α * tB α (ρ, w)) * tF (ρ, w) γ ≤ (q / 2 + 6) * ∑ w, tF (ρ, w) γ :=
              wsum_le _ _ _ (fun w => hSE w) (fun w => htF0 _ _)
          _ ≤ (q / 2 + 6) * (2 * q) := mul_le_mul_of_nonneg_left (hFE γ) (by positivity))
      (fun s hs0 hsρ => wsum_le' _ _ 2 (fun w => hπ2nn _) (fun w => hFG s w γ hs0 hsρ))
    have hπ2s' : ∑ s, ∑ w, ∑ α, π α * tB α (s, w) ≤ q * q := by
      calc ∑ s, ∑ w, ∑ α, π α * tB α (s, w) = ∑ β, ∑ α, π α * tB α β :=
            (Fintype.sum_prod_type (fun β => ∑ α, π α * tB α β)).symm
        _ ≤ q * q := hπ2s
    try beta_reduce at hsplit
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q - 12) hq0.le]

/-- the concrete instance: PD layer B = J ∘ F and final layer F on (F × F, cadd (star e)),
ρ = e.symm (Pi.single i 1) of weight one, normalised tables T = ddtC / q². -/
theorem two_step_pd {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h : F → F) (K : F →+ F) (ε : F)
    (i : Fin m)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = e.symm (Pi.single i 1))) (hε : ∀ a, ε + K a ≠ 0)
    (hp : Function.Injective p)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (hq : 12 ≤ (Fintype.card F : ℝ))
    (π : F × F → ℝ) (hπ0 : ∀ α, 0 ≤ π α) (hπs : ∑ α, π α ≤ 1) (hπz : π 0 = 0)
    (hπx : ∀ α, π α ≤ 1 / (Fintype.card F : ℝ)) (γ : F × F) :
    ∑ β, (∑ α, π α * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F)))
      * ((ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) β γ : ℝ)
        / ((Fintype.card F : ℝ) * Fintype.card F))
      ≤ 4 / ((Fintype.card F : ℝ) * Fintype.card F) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hρ : e.symm (Pi.single i (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have h1 := congrArg e h0
    rw [AddEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 i
    simp at h2
  have hd0 : ∀ a, (fun a => ε + K a) a ≠ 0 := hε
  have hKρ : K (e.symm (Pi.single i 1)) = 0 := (hker _).2 (Or.inr rfl)
  have hdρ : ∀ a, (fun a => ε + K a) (a + e.symm (Pi.single i 1)) = (fun a => ε + K a) a + 0 := by
    intro a; simp only [map_add, hKρ, add_zero]
  have hG : ∀ u, u ≠ 0 → u ≠ e.symm (Pi.single i 1) →
      K u ≠ 0 ∧ ∀ a, (fun a => ε + K a) (a + u) = (fun a => ε + K a) a + K u := by
    intro u hu0 huρ
    refine ⟨fun h0 => ?_, fun a => ?_⟩
    · rcases (hker u).1 h0 with h1 | h1
      · exact hu0 h1
      · exact huρ h1
    · simp only [map_add]; ring
  have hapnρ := hapn _ hρ
  -- the count facts (cast to ℝ)
  have key := two_step_abstract
    (fun α β => (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ))
    (fun β γ => (ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) β γ : ℝ))
    π (e.symm (Pi.single i 1)) hρ q (1 / q) hq (by positivity) (one_div_mul_cancel hq0.ne')
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (fun v t hv => by
      try dsimp only
      rw [colB_ZZ e p h (fun a => ε + K a) hd0 v hv t, Nat.cast_zero])
    (fun t => by
      have h1 := colB_ZE e p h (fun a => ε + K a) hd0 (e.symm (Pi.single i 1)) hρ t
      have h2 : (2 : ℝ) * ∑ v, (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a))
          ((0 : F), v) (e.symm (Pi.single i 1), t) : ℝ) ≤ q * q := by
        rw [hqdef]; exact_mod_cast h1
      try dsimp only
      linarith)
    (fun t => by
      have h1 := colB_EZ e p h (fun a => ε + K a) hd0 (e.symm (Pi.single i 1)) hapnρ t
      have h2 : ∑ v, (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a))
          (e.symm (Pi.single i 1), v) ((0 : F), t) : ℝ) ≤ 2 * q := by
        rw [hqdef]; exact_mod_cast h1
      try dsimp only
      exact h2)
    (fun t => by
      have h1 := colB_EE e p h (fun a => ε + K a) hd0 i hapnρ t
      have h2 : ∑ v, (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a))
          (e.symm (Pi.single i 1), v) (e.symm (Pi.single i 1), t) : ℝ) ≤ 2 * q := by
        rw [hqdef]; exact_mod_cast h1
      try dsimp only
      exact h2)
    (fun u v t hu0 huρ => by
      obtain ⟨hk, hd⟩ := hG u hu0 huρ
      have h1 := entB_GZ e p h (fun a => ε + K a) u v (K u) hk hd (hapn u hu0) t
      try dsimp only
      exact_mod_cast h1)
    (fun u v t hu0 huρ => by
      obtain ⟨hk, hd⟩ := hG u hu0 huρ
      have h1 := entB_GE e p h (fun a => ε + K a) u v (K u) hk hd (hapn u hu0) i t
      try dsimp only
      exact_mod_cast h1)
    (fun α => by
      have h1 := rowsum_le (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α
      rw [Fintype.card_prod] at h1
      have h2 : ∑ β, (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ) ≤ q * q := by
        rw [hqdef]; exact_mod_cast h1
      try dsimp only
      exact h2)
    (fun u v γ hu hγ => by
      try dsimp only
      rw [colF_low0_nonZ e p h (fun a => ε + K a) hp u v hu γ hγ, Nat.cast_zero])
    (fun γ => by
      have h1 := colF_Z e p h (fun a => ε + K a) hd0 γ
      have h2 : ∑ v, (ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) ((0 : F), v) γ : ℝ)
          ≤ q * q := by
        rw [hqdef]; exact_mod_cast h1
      try dsimp only
      exact h2)
    (fun v γ hγ => by
      try dsimp only
      rw [colF_lowne_Z e p h (fun a => ε + K a) v γ hγ, Nat.cast_zero])
    (fun γ => by
      have h1 := colF_E e p h (fun a => ε + K a) hd0 (e.symm (Pi.single i 1)) hapnρ γ
      have h2 : ∑ v, (ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a))
          (e.symm (Pi.single i 1), v) γ : ℝ) ≤ 2 * q := by
        rw [hqdef]; exact_mod_cast h1
      try dsimp only
      exact h2)
    (fun u v γ hu0 huρ => by
      obtain ⟨hk, hd⟩ := hG u hu0 huρ
      have h1 := entF_G e p h (fun a => ε + K a) u v (K u) hk hd (hapn u hu0) γ
      try dsimp only
      exact_mod_cast h1)
    hπ0 hπs hπz hπx γ
  -- normalise
  have hN : 0 < q * q := by positivity
  have hrw : ∀ β, (∑ α, π α * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ)
        / (q * q))) * ((ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) β γ : ℝ) / (q * q))
      = ((∑ α, π α * (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ))
          * (ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) β γ : ℝ)) / ((q * q) * (q * q)) := by
    intro β
    have hs : ∑ α, π α * ((ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ) / (q * q))
        = (∑ α, π α * (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ)) / (q * q) := by
      rw [sum_div]; refine sum_congr rfl (fun α _ => by ring)
    rw [hs]; ring
  simp_rw [hrw]
  rw [← sum_div, div_le_div_iff₀ (by positivity) hN]
  calc (∑ β, (∑ α, π α * (ddtC (ApnCipherC7.star e) (pdB p h (fun a => ε + K a)) α β : ℝ))
          * (ddtC (ApnCipherC7.star e) (pdF p h (fun a => ε + K a)) β γ : ℝ)) * (q * q)
      ≤ (4 * (q * q)) * (q * q) := mul_le_mul_of_nonneg_right key hN.le
    _ = 4 * ((q * q) * (q * q)) := by ring

end ApnCipherC8

end
