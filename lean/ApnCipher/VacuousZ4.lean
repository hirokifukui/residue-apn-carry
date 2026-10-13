/-
P9-02 (C9, Claude 2026-10-12): ONE component -- the hypotheses of C8 `ApnCipherC8.w2_Z4_le` on the
mixer are jointly unsatisfiable.  `Z4m m = Fin m → ZMod 4` carries the POINTWISE ring structure; a unit
of ZMod 4 is 1 or 3, so at any coordinate i the four unit entries reduce to 1 mod 2 and the determinant
m11*m22 - m12*m21 takes the value 0 or 2 there, which is not a unit.  The coordinate i : Fin m that
`w2_Z4_le` already takes forces m > 0.  Hence `w2_Z4_le` is a true implication with no instance
(vacuous); it is NOT a verification of a concrete mixer.  C8 files and logs are unchanged.
The repair (additive automorphisms instead of pointwise scalars) is `MixAdd.lean` / `ThetaZ4.lean`.
-/
import ApnCipher.DigitSplit_v2

noncomputable section

namespace ApnCipherC9

open ApnCipherC8

/-- units of ZMod 4 are 1 and 3. -/
theorem zmod4_unit_cases : ∀ a b : ZMod 4, a * b = 1 → a = 1 ∨ a = 3 := by decide

/-- 2×2 determinants with entries in {1, 3} are 0 or 2 in ZMod 4. -/
theorem zmod4_det_cases : ∀ a b c d : ZMod 4, (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) →
    (c = 1 ∨ c = 3) → (d = 1 ∨ d = 3) → (a * d - b * c = 0 ∨ a * d - b * c = 2) := by decide

/-- neither 0 nor 2 is a unit of ZMod 4. -/
theorem zmod4_nonunit_02 : ∀ x y : ZMod 4, (x = 0 ∨ x = 2) → x * y ≠ 1 := by decide

theorem zmod4_isUnit_cases {a : ZMod 4} (ha : IsUnit a) : a = 1 ∨ a = 3 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  exact zmod4_unit_cases a b hb

/-- evaluation at a coordinate, as a ring homomorphism of the pointwise ring. -/
def evalZ (m : ℕ) (i : Fin m) : Z4m m →+* ZMod 4 :=
  Pi.evalRingHom (fun _ : Fin m => ZMod 4) i

/-- C8-F01: the five unit hypotheses of `w2_Z4_le` contradict each other (any m, given i : Fin m). -/
theorem w2_Z4_mixer_hyps_false {m : ℕ} (i : Fin m) {m11 m12 m21 m22 : Z4m m}
    (h11 : IsUnit m11) (h12 : IsUnit m12) (h21 : IsUnit m21) (h22 : IsUnit m22)
    (hdet : IsUnit (m11 * m22 - m12 * m21)) : False := by
  have u11 := zmod4_isUnit_cases (h11.map (evalZ m i))
  have u12 := zmod4_isUnit_cases (h12.map (evalZ m i))
  have u21 := zmod4_isUnit_cases (h21.map (evalZ m i))
  have u22 := zmod4_isUnit_cases (h22.map (evalZ m i))
  have ud := hdet.map (evalZ m i)
  rw [map_sub, map_mul, map_mul] at ud
  obtain ⟨y, hy⟩ := ud.exists_right_inv
  exact zmod4_nonunit_02 _ y
    (zmod4_det_cases _ _ _ _ u11 u12 u21 u22) hy

/-- the same, as a non-existence statement: no mixer satisfies the hypotheses of `w2_Z4_le`. -/
theorem no_unit_mds_Z4m {m : ℕ} (i : Fin m) :
    ¬ ∃ m11 m12 m21 m22 : Z4m m, IsUnit m11 ∧ IsUnit m12 ∧ IsUnit m21 ∧ IsUnit m22 ∧
      IsUnit (m11 * m22 - m12 * m21) := by
  rintro ⟨m11, m12, m21, m22, h11, h12, h21, h22, hdet⟩
  exact w2_Z4_mixer_hyps_false i h11 h12 h21 h22 hdet

/-- the coordinate argument of `w2_Z4_le` forces m > 0 (no escape through the empty index type). -/
theorem pos_of_fin {m : ℕ} (i : Fin m) : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt

end ApnCipherC9

end
