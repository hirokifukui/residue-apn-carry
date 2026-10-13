/-
P8-10 (C8, Claude 2026-10-12): ONE component -- the semantic correspondence for the ADDITIVE group of
(ZMod 4)^m: the digit split z = lo(z) + 2·hi(z) coordinatewise gives an explicit bijection
  phi4 e : (Fin m → ZMod 4) ≃ F × F,   x ↦ (e⁻¹(lo ∘ x), e⁻¹(hi ∘ x)),
for ANY field F with an additive basis map e : F ≃+ (Fin m → ZMod 2) (e.g. e = a fixed F₂-basis of F_q),
and phi4_add proves the carry identity  phi4 (x + y) = cadd (star e) (phi4 x) (phi4 y)
(paper Lemma "Carry": (a,b)+(u,v) = (a⊕u, b⊕v⊕(a⋆u))).  The digit facts on ZMod 4 are checked by `decide`.
Consequence w2_Z4_le: C5 w2_split_tail_le for R = (Fin m → ZMod 4) with the actual local blocks S2w / S2,
with hφ discharged; remaining hypotheses: PD, ρ weight one, 12 ≤ q, C5 structural hypotheses.
NOT here: the ring multiplication of GR(4,m) (not used by any differential statement; the mixer entries
m_ij are then elements of the pointwise ring (ZMod 4)^m, not of GR(4,m)).
-/
import ApnCipher.Bridge
-- v2: build 1 of DigitSplit.lean exit 1 (instance search for Fintype of the 6-fold key product over
--     Fin m → ZMod 4 failed); (ZMod 4)^m wrapped as the type Z4m m with its Pi instances; proofs unchanged.

noncomputable section

open Finset

namespace ApnCipherC8

open ApnCipherC7

/-- low digit of z ∈ ZMod 4. -/
def lo4 (z : ZMod 4) : ZMod 2 := (z.val : ZMod 2)

/-- high digit of z ∈ ZMod 4. -/
def hi4 (z : ZMod 4) : ZMod 2 := ((z.val / 2 : ℕ) : ZMod 2)

/-- recombination a + 2b. -/
def comb4 (a b : ZMod 2) : ZMod 4 := (a.val : ZMod 4) + 2 * (b.val : ZMod 4)

theorem lo4_add : ∀ z w : ZMod 4, lo4 (z + w) = lo4 z + lo4 w := by decide

theorem hi4_add : ∀ z w : ZMod 4, hi4 (z + w) = hi4 z + hi4 w + lo4 z * lo4 w := by decide

theorem comb4_lo_hi : ∀ z : ZMod 4, comb4 (lo4 z) (hi4 z) = z := by decide

theorem lo4_comb : ∀ a b : ZMod 2, lo4 (comb4 a b) = a := by decide

theorem hi4_comb : ∀ a b : ZMod 2, hi4 (comb4 a b) = b := by decide

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- the two-digit coordinate map of (ZMod 4)^m. -/
def phi4 {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) : (Fin m → ZMod 4) ≃ F × F where
  toFun x := (e.symm (fun i => lo4 (x i)), e.symm (fun i => hi4 (x i)))
  invFun z := fun i => comb4 (e z.1 i) (e z.2 i)
  left_inv x := by
    funext i
    simp only [AddEquiv.apply_symm_apply]
    exact comb4_lo_hi (x i)
  right_inv z := by
    refine Prod.ext ?_ ?_
    · show e.symm (fun i => lo4 (comb4 (e z.1 i) (e z.2 i))) = z.1
      have h1 : (fun i => lo4 (comb4 (e z.1 i) (e z.2 i))) = e z.1 :=
        funext (fun i => lo4_comb _ _)
      rw [h1, AddEquiv.symm_apply_apply]
    · show e.symm (fun i => hi4 (comb4 (e z.1 i) (e z.2 i))) = z.2
      have h1 : (fun i => hi4 (comb4 (e z.1 i) (e z.2 i))) = e z.2 :=
        funext (fun i => hi4_comb _ _)
      rw [h1, AddEquiv.symm_apply_apply]

omit [Fintype F] [DecidableEq F] in
/-- the carry identity hφ for the additive group of (ZMod 4)^m. -/
theorem phi4_add {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (x y : Fin m → ZMod 4) :
    phi4 e (x + y) = cadd (ApnCipherC7.star e) (phi4 e x) (phi4 e y) := by
  refine Prod.ext ?_ ?_
  · show e.symm (fun i => lo4 ((x + y) i))
      = e.symm (fun i => lo4 (x i)) + e.symm (fun i => lo4 (y i))
    rw [← map_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    exact lo4_add _ _
  · show e.symm (fun i => hi4 ((x + y) i))
      = e.symm (fun i => hi4 (x i)) + e.symm (fun i => hi4 (y i))
        + ApnCipherC7.star e (e.symm (fun i => lo4 (x i))) (e.symm (fun i => lo4 (y i)))
    unfold ApnCipherC7.star
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← map_add, ← map_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    exact hi4_add _ _

/-- (ZMod 4)^m as a named type (same Pi instances), so instance search treats it as an atom. -/
def Z4m (m : ℕ) : Type := Fin m → ZMod 4

instance (m : ℕ) : CommRing (Z4m m) := inferInstanceAs (CommRing (Fin m → ZMod 4))
instance (m : ℕ) : Fintype (Z4m m) := inferInstanceAs (Fintype (Fin m → ZMod 4))
instance (m : ℕ) : DecidableEq (Z4m m) := inferInstanceAs (DecidableEq (Fin m → ZMod 4))

/-- phi4 on the named type. -/
def phi4Z {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) : Z4m m ≃ F × F := phi4 e

omit [Fintype F] [DecidableEq F] in
theorem phi4Z_add {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (x y : Z4m m) :
    phi4Z e (x + y) = cadd (ApnCipherC7.star e) (phi4Z e x) (phi4Z e y) :=
  phi4_add e x y

/-- C5 w2_split_tail_le on R = Z4m m = (ZMod 4)^m with the actual local blocks; hφ is now a theorem. -/
theorem w2_Z4_le {m : ℕ} (e : F ≃+ (Fin m → ZMod 2))
    (p h : F → F) (K : F →+ F) (ε : F) (i : Fin m)
    (hker : ∀ u, K u = 0 ↔ (u = 0 ∨ u = e.symm (Pi.single i 1))) (hε : ∀ a, ε + K a ≠ 0)
    (hp : Function.Injective p)
    (hapn : ∀ u, u ≠ 0 → ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u)
    (hq : 12 ≤ (Fintype.card F : ℝ))
    {m11 m12 m21 m22 : Z4m m} (h11 : IsUnit m11) (h12 : IsUnit m12) (h21 : IsUnit m21)
    (h22 : IsUnit m22) (hdet : IsUnit (m11 * m22 - m12 * m21))
    {κ5 κ6 : Type*} [Fintype κ5] [Nonempty κ5] [Fintype κ6] [Nonempty κ6]
    (M2 M3 : (Z4m m × Z4m m) ≃+ (Z4m m × Z4m m))
    (C3 : κ5 → (Z4m m × Z4m m) ≃ (Z4m m × Z4m m))
    (C4 : κ6 → (Z4m m × Z4m m) ≃ (Z4m m × Z4m m))
    {α : Z4m m × Z4m m} (hα : α ≠ 0)
    (γ : Z4m m × Z4m m) :
    ApnCipherC5.avgDP
      (ApnCipherC5.compK (ApnCipherC5.compK (ApnCipherC5.compK
        (ApnCipherC5.parK (S2w (phi4Z e) p h (fun a => ε + K a) hp hε)
          (S2w (phi4Z e) p h (fun a => ε + K a) hp hε))
        (ApnCipherC5.mix2 m11 m12 m21 m22 hdet)
        (ApnCipherC5.parE (S2 (phi4Z e) p h (fun a => ε + K a) hp hε)
          (S2 (phi4Z e) p h (fun a => ε + K a) hp hε)))
        M2 C3) M3 C4) α γ
      ≤ (4 / (Fintype.card (Z4m m) : ℝ)) ^ 2 :=
  w2_pd_le e (phi4Z e) (phi4Z_add e) p h K ε i hker hε hp hapn hq h11 h12 h21 h22 hdet
    M2 M3 C3 C4 hα γ

end ApnCipherC8

end
