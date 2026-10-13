/-
P9-04 (C9, Claude 2026-10-12): ONE component -- the non-vacuous concrete instance.
* `mixTheta Θ N`: the two-word mixer M(x,y) = (x + y, x + Θ y) on A × A for an additive automorphism Θ of A
  and a two-sided inverse N of y ↦ Θ y - y (i.e. Θ - I invertible).  Inverse: y = N(v - u), x = u - y.
  `mixTheta_mds`: its four partial maps are id, id, id, Θ, all bijective (IsMDS2A).
* `w2_Z4_theta_le`: on A = Z4m m (additive group of (ZMod 4)^m, digit map phi4Z e with phi4Z_add proved in
  C8), with the actual local blocks S2w / S2 of C8 Bridge and two reset layers, the real key average of the
  (2,2,1,1) w = 2 arrangement is ≤ (4/N)², N = |Z4m m| = q².  No ring-scalar mixer hypothesis.
* `theta5`, `n5`: an explicit witness for m = 5.  theta5 is multiplication by t in Z4[t]/(t^5 + t^2 + 1)
  in the coefficient basis 1, t, ..., t^4 (c ↦ (-c4, c0, c1 - c4, c2, c3)); its inverse is theta5_inv;
  n5 is the inverse of theta5 - I (matrix [[2,3,3,3,3],[2,2,3,3,3],[1,1,1,2,2],[1,1,1,1,2],[1,1,1,1,1]]).
  `theta5_mixer_mds` shows the mixer hypotheses are satisfied (non-empty).
  v2: run 1 (ThetaZ4.lean) exit 1 only in theta5_N1 (Z4m 5 vs Fin 5 → ZMod 4 elaboration) and in an extra
  remark theta5_not_pointwise (dropped; VacuousZ4 already shows no pointwise-scalar mixer exists).
  v3: = v2 + section Final5 (w2_Z4_theta5_le); the v2 run built the file before Final5 was appended.  The PD hypotheses on F
  (APN p, K, ε) are not instantiated here; they are the C8 local hypotheses, witnessed on paper / finite checks.
-/
import ApnCipher.MixAdd
import ApnCipher.DigitSplit_v2

noncomputable section

open Finset

namespace ApnCipherC9

open ApnCipherC8

section Theta

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- M(x,y) = (x + y, x + Θ y), with N a two-sided inverse of Θ - I. -/
def mixTheta (Θ : A ≃+ A) (N : A → A) (hN1 : ∀ y, N (Θ y - y) = y)
    (hN2 : ∀ v, Θ (N v) - N v = v) : (A × A) ≃+ (A × A) where
  toFun d := (d.1 + d.2, d.1 + Θ d.2)
  invFun e := (e.1 - N (e.2 - e.1), N (e.2 - e.1))
  left_inv d := by
    obtain ⟨x, y⟩ := d
    have h : (x + Θ y) - (x + y) = Θ y - y := by abel
    show ((x + y) - N ((x + Θ y) - (x + y)), N ((x + Θ y) - (x + y))) = (x, y)
    rw [h, hN1]
    ext <;> simp
  right_inv e := by
    obtain ⟨u, v⟩ := e
    have h2 := hN2 (v - u)
    show (u - N (v - u) + N (v - u), u - N (v - u) + Θ (N (v - u))) = (u, v)
    have h3 : u - N (v - u) + Θ (N (v - u)) = u + (Θ (N (v - u)) - N (v - u)) := by abel
    rw [h3, h2]
    ext
    · simp
    · show u + (v - u) = v
      abel
  map_add' x y := by
    ext
    · show (x + y).1 + (x + y).2 = (x.1 + x.2) + (y.1 + y.2)
      simp only [Prod.fst_add, Prod.snd_add]; abel
    · show (x + y).1 + Θ (x + y).2 = (x.1 + Θ x.2) + (y.1 + Θ y.2)
      simp only [Prod.fst_add, Prod.snd_add, map_add]; abel

theorem mixTheta_apply (Θ : A ≃+ A) (N : A → A) (hN1 : ∀ y, N (Θ y - y) = y)
    (hN2 : ∀ v, Θ (N v) - N v = v) (d : A × A) :
    mixTheta Θ N hN1 hN2 d = (d.1 + d.2, d.1 + Θ d.2) := rfl

/-- the mixer is MDS in the additive sense: partial maps id, id, id, Θ. -/
theorem mixTheta_mds (Θ : A ≃+ A) (N : A → A) (hN1 : ∀ y, N (Θ y - y) = y)
    (hN2 : ∀ v, Θ (N v) - N v = v) : IsMDS2A (mixTheta Θ N hN1 hN2) := by
  have e11 : (c11 (mixTheta Θ N hN1 hN2) : A → A) = id := by
    funext x; simp [c11, mixTheta_apply]
  have e12 : (c12 (mixTheta Θ N hN1 hN2) : A → A) = id := by
    funext x; simp [c12, mixTheta_apply]
  have e21 : (c21 (mixTheta Θ N hN1 hN2) : A → A) = id := by
    funext x; simp [c21, mixTheta_apply]
  have e22 : (c22 (mixTheta Θ N hN1 hN2) : A → A) = Θ := by
    funext x; simp [c22, mixTheta_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e11]; exact Function.bijective_id
  · rw [e12]; exact Function.bijective_id
  · rw [e21]; exact Function.bijective_id
  · rw [e22]; exact Θ.bijective

/-- the mixer is injective on pairs; in particular (Θ - I) injective is what is used. -/
theorem mixTheta_injective (Θ : A ≃+ A) (N : A → A) (hN1 : ∀ y, N (Θ y - y) = y)
    (hN2 : ∀ v, Θ (N v) - N v = v) : Function.Injective (mixTheta Θ N hN1 hN2) :=
  (mixTheta Θ N hN1 hN2).injective

end Theta

section Final

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- P9-04: non-vacuous concrete two-word statement on (ZMod 4)^m (additive group) with the additive mixer
(x, y) ↦ (x + y, x + Θ y): the real key average of the (2,2,1,1), w = 2 arrangement is ≤ (4/N)². -/
theorem w2_Z4_theta_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2))
    (p h : F → F) (K : F →+ F) (ε : F) (i : Fin m)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = e.symm (Pi.single i 1))) (hε : ∀ a, ε + K a ≠ 0)
    (hp : Function.Injective p)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (hq : 12 ≤ (Fintype.card F : ℝ))
    (Θ : Z4m m ≃+ Z4m m) (N : Z4m m → Z4m m) (hN1 : ∀ y, N (Θ y - y) = y)
    (hN2 : ∀ v, Θ (N v) - N v = v)
    {κ5 κ6 : Type*} [Fintype κ5] [Nonempty κ5] [Fintype κ6] [Nonempty κ6]
    (M2 M3 : (Z4m m × Z4m m) ≃+ (Z4m m × Z4m m))
    (C3 : κ5 → (Z4m m × Z4m m) ≃ (Z4m m × Z4m m))
    (C4 : κ6 → (Z4m m × Z4m m) ≃ (Z4m m × Z4m m))
    {α : Z4m m × Z4m m} (hα : α ≠ 0) (γ : Z4m m × Z4m m) :
    ApnCipherC5.avgDP
      (ApnCipherC5.compK (ApnCipherC5.compK (ApnCipherC5.compK
        (parKA (S2w (phi4Z e) p h (fun a => ε + K a) hp hε)
          (S2w (phi4Z e) p h (fun a => ε + K a) hp hε))
        (mixTheta Θ N hN1 hN2)
        (parEA (S2 (phi4Z e) p h (fun a => ε + K a) hp hε)
          (S2 (phi4Z e) p h (fun a => ε + K a) hp hε)))
        M2 C3) M3 C4) α γ
      ≤ (4 / (Fintype.card (Z4m m) : ℝ)) ^ 2 := by
  have hinj : ∀ k, Function.Injective (S2w (phi4Z e) p h (fun a => ε + K a) hp hε k) := by
    intro k x y hxy
    have h1 : x + k.1 = y + k.1 := (S2 (phi4Z e) p h (fun a => ε + K a) hp hε k.2).injective hxy
    exact add_right_cancel h1
  have hb : ∀ a b : Z4m m, a ≠ 0 →
      ApnCipherC5.avgDP (S2w (phi4Z e) p h (fun a => ε + K a) hp hε) a b
        ≤ 4 / (Fintype.card (Z4m m) : ℝ) := by
    intro a b ha
    rw [avgDP_S2w_eq]
    exact avgDP_S2_le e (phi4Z e) (phi4Z_add e) p h K ε i hker hε hp hapn hq a b ha
  have hb' : ∀ a b : Z4m m, a ≠ 0 →
      ApnCipherC5.avgDP (fun k => (S2 (phi4Z e) p h (fun a => ε + K a) hp hε k : Z4m m → Z4m m)) a b
        ≤ 4 / (Fintype.card (Z4m m) : ℝ) :=
    fun a b ha => avgDP_S2_le e (phi4Z e) (phi4Z_add e) p h K ε i hker hε hp hapn hq a b ha
  exact w2A_split_tail_le _ _ _ _ hinj hinj (mixTheta Θ N hN1 hN2) (mixTheta_mds Θ N hN1 hN2)
    M2 M3 C3 C4 (by positivity) hb hb hb' hb' hα γ

end Final

section Witness5

/-- multiplication by t in Z4[t]/(t^5 + t^2 + 1), coefficient basis. -/
def th5f (c : Fin 5 → ZMod 4) : Fin 5 → ZMod 4 := ![-(c 4), c 0, c 1 - c 4, c 2, c 3]

/-- multiplication by t⁻¹ = -(t^4 + t). -/
def th5i (d : Fin 5 → ZMod 4) : Fin 5 → ZMod 4 := ![d 1, d 2 - d 0, d 3, d 4, -(d 0)]

/-- (Θ - I)⁻¹ over ZMod 4. -/
def n5 (d : Fin 5 → ZMod 4) : Fin 5 → ZMod 4 :=
  ![2 * d 0 + 3 * d 1 + 3 * d 2 + 3 * d 3 + 3 * d 4,
    2 * d 0 + 2 * d 1 + 3 * d 2 + 3 * d 3 + 3 * d 4,
    1 * d 0 + 1 * d 1 + 1 * d 2 + 2 * d 3 + 2 * d 4,
    1 * d 0 + 1 * d 1 + 1 * d 2 + 1 * d 3 + 2 * d 4,
    1 * d 0 + 1 * d 1 + 1 * d 2 + 1 * d 3 + 1 * d 4]

theorem four_eq_zero : (4 : ZMod 4) = 0 := by decide

theorem th5_left (c : Fin 5 → ZMod 4) : th5i (th5f c) = c := by
  funext i; fin_cases i <;> simp [th5f, th5i]

theorem th5_right (d : Fin 5 → ZMod 4) : th5f (th5i d) = d := by
  funext i; fin_cases i <;> simp [th5f, th5i]

theorem th5_add (x y : Fin 5 → ZMod 4) : th5f (x + y) = th5f x + th5f y := by
  funext i; fin_cases i <;> simp [th5f] <;> ring

-- coordinate identities (each is an integer identity up to a multiple of 4)
theorem n1c0 (a b c d e : ZMod 4) :
    2 * (-e - a) + 3 * (a - b) + 3 * (b - e - c) + 3 * (c - d) + 3 * (d - e) = a := by
  linear_combination (-2 * e) * four_eq_zero
theorem n1c1 (a b c d e : ZMod 4) :
    2 * (-e - a) + 2 * (a - b) + 3 * (b - e - c) + 3 * (c - d) + 3 * (d - e) = b := by
  linear_combination (-2 * e) * four_eq_zero
theorem n1c2 (a b c d e : ZMod 4) :
    1 * (-e - a) + 1 * (a - b) + 1 * (b - e - c) + 2 * (c - d) + 2 * (d - e) = c := by
  linear_combination (-1 * e) * four_eq_zero
theorem n1c3 (a b c d e : ZMod 4) :
    1 * (-e - a) + 1 * (a - b) + 1 * (b - e - c) + 1 * (c - d) + 2 * (d - e) = d := by
  linear_combination (-1 * e) * four_eq_zero
theorem n1c4 (a b c d e : ZMod 4) :
    1 * (-e - a) + 1 * (a - b) + 1 * (b - e - c) + 1 * (c - d) + 1 * (d - e) = e := by
  linear_combination (-1 * e) * four_eq_zero

theorem n2c0 (a b c d e : ZMod 4) :
    -(1 * a + 1 * b + 1 * c + 1 * d + 1 * e) - (2 * a + 3 * b + 3 * c + 3 * d + 3 * e) = a := by
  linear_combination (-1 * a + -1 * b + -1 * c + -1 * d + -1 * e) * four_eq_zero
theorem n2c1 (a b c d e : ZMod 4) :
    (2 * a + 3 * b + 3 * c + 3 * d + 3 * e) - (2 * a + 2 * b + 3 * c + 3 * d + 3 * e) = b := by
  ring
theorem n2c2 (a b c d e : ZMod 4) :
    (2 * a + 2 * b + 3 * c + 3 * d + 3 * e) - (1 * a + 1 * b + 1 * c + 1 * d + 1 * e)
      - (1 * a + 1 * b + 1 * c + 2 * d + 2 * e) = c := by
  ring
theorem n2c3 (a b c d e : ZMod 4) :
    (1 * a + 1 * b + 1 * c + 2 * d + 2 * e) - (1 * a + 1 * b + 1 * c + 1 * d + 2 * e) = d := by
  ring
theorem n2c4 (a b c d e : ZMod 4) :
    (1 * a + 1 * b + 1 * c + 1 * d + 2 * e) - (1 * a + 1 * b + 1 * c + 1 * d + 1 * e) = e := by
  ring

theorem n5_left (y : Fin 5 → ZMod 4) : n5 (th5f y - y) = y := by
  funext i
  fin_cases i
  · exact n1c0 (y 0) (y 1) (y 2) (y 3) (y 4)
  · exact n1c1 (y 0) (y 1) (y 2) (y 3) (y 4)
  · exact n1c2 (y 0) (y 1) (y 2) (y 3) (y 4)
  · exact n1c3 (y 0) (y 1) (y 2) (y 3) (y 4)
  · exact n1c4 (y 0) (y 1) (y 2) (y 3) (y 4)

theorem n5_right (v : Fin 5 → ZMod 4) : th5f (n5 v) - n5 v = v := by
  funext i
  fin_cases i
  · exact n2c0 (v 0) (v 1) (v 2) (v 3) (v 4)
  · exact n2c1 (v 0) (v 1) (v 2) (v 3) (v 4)
  · exact n2c2 (v 0) (v 1) (v 2) (v 3) (v 4)
  · exact n2c3 (v 0) (v 1) (v 2) (v 3) (v 4)
  · exact n2c4 (v 0) (v 1) (v 2) (v 3) (v 4)

/-- Θ for m = 5 as an additive automorphism of Z4m 5. -/
def theta5 : Z4m 5 ≃+ Z4m 5 where
  toFun := th5f
  invFun := th5i
  left_inv := th5_left
  right_inv := th5_right
  map_add' := th5_add

/-- (Θ - I)⁻¹ as a map of Z4m 5. -/
def n5Z (v : Z4m 5) : Z4m 5 := n5 v

theorem theta5_N1 (y : Z4m 5) : n5Z (theta5 y - y) = y := n5_left y
theorem theta5_N2 (v : Z4m 5) : theta5 (n5Z v) - n5Z v = v := n5_right v

/-- non-emptiness: the mixer hypotheses of `w2_Z4_theta_le` are satisfied for m = 5. -/
theorem theta5_mixer_mds : IsMDS2A (mixTheta theta5 n5Z theta5_N1 theta5_N2) :=
  mixTheta_mds theta5 n5Z theta5_N1 theta5_N2

end Witness5

section Final5

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- m = 5 with the explicit mixer theta5: only the PD hypotheses on (p, K, ε) remain. -/
theorem w2_Z4_theta5_le (e : F ≃+ (Fin 5 → ZMod 2))
    (p h : F → F) (K : F →+ F) (ε : F) (i : Fin 5)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = e.symm (Pi.single i 1))) (hε : ∀ a, ε + K a ≠ 0)
    (hp : Function.Injective p)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (hq : 12 ≤ (Fintype.card F : ℝ))
    {κ5 κ6 : Type*} [Fintype κ5] [Nonempty κ5] [Fintype κ6] [Nonempty κ6]
    (M2 M3 : (Z4m 5 × Z4m 5) ≃+ (Z4m 5 × Z4m 5))
    (C3 : κ5 → (Z4m 5 × Z4m 5) ≃ (Z4m 5 × Z4m 5))
    (C4 : κ6 → (Z4m 5 × Z4m 5) ≃ (Z4m 5 × Z4m 5))
    {α : Z4m 5 × Z4m 5} (hα : α ≠ 0) (γ : Z4m 5 × Z4m 5) :
    ApnCipherC5.avgDP
      (ApnCipherC5.compK (ApnCipherC5.compK (ApnCipherC5.compK
        (parKA (S2w (phi4Z e) p h (fun a => ε + K a) hp hε)
          (S2w (phi4Z e) p h (fun a => ε + K a) hp hε))
        (mixTheta theta5 n5Z theta5_N1 theta5_N2)
        (parEA (S2 (phi4Z e) p h (fun a => ε + K a) hp hε)
          (S2 (phi4Z e) p h (fun a => ε + K a) hp hε)))
        M2 C3) M3 C4) α γ
      ≤ (4 / (Fintype.card (Z4m 5) : ℝ)) ^ 2 :=
  w2_Z4_theta_le e p h K ε i hker hε hp hapn hq theta5 n5Z theta5_N1 theta5_N2 M2 M3 C3 C4 hα γ

end Final5

end ApnCipherC9

end
