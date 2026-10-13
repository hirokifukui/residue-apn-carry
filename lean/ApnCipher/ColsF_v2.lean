/-
P8-08 part 2 (C8, Claude 2026-10-12): ONE component -- the final-layer part of the paper's Prop. "table"
for F = F_{p,d,h} : (a, b) ↦ (p a, h a + d a · b) on concrete carry coordinates (counts of ddtC):
  memF            : Lemma diffF in carry form (the two coordinate equations of F(x ⊕ α) = F(x) ⊕ γ)
  colF_low0_nonZ  : γ low digit 0, row (u, v) with u ≠ 0  ⇒ entry 0     (p injective)
  colF_Z          : Σ_v ddtC((0, v), γ) ≤ q · q = N   (every γ; = "Z column sum ≤ 1")
  colF_lowne_Z    : γ low digit ≠ 0, row (0, v)         ⇒ entry 0
  colF_E          : Σ_v ddtC((ρ, v), γ) ≤ 2q            (APN along ρ; any ρ)
  entF_G          : u with d(a+u) = d a + k, k ≠ 0      ⇒ entry ≤ 2
Plus generic facts used by the two-step bound: rowsum_le (Σ_β ddtC(α, β) ≤ |F × F|),
ddtC_to_zero (injective map, α ≠ 0 ⇒ ddtC(α, 0) = 0), pdB_injective, pdF_injective.
-/
import ApnCipher.ColsB_v3
-- v2: build 1 of ColsF.lean exit 1 (import resolution: c7 build dir shadowed c8 build; not a proof error).
--     Content unchanged; built with check_v2.sh (single build dir).

noncomputable section

open Finset

namespace ApnCipherC8

open ApnCipherC7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- the final layer F = F_{p,d,h} in two-digit coordinates (paper sec. 2: (a,b) ↦ (p(a), h(a) ⊕ d(a) b)). -/
def pdF (p h d : F → F) (x : F × F) : F × F := (p x.1, h x.1 + d x.1 * x.2)

/-- Lemma diffF in carry form. -/
theorem memF {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (x α γ : F × F) :
    pdF p h d (cadd (ApnCipherC7.star e) x α) = cadd (ApnCipherC7.star e) (pdF p h d x) γ ↔
    (p (x.1 + α.1) = p x.1 + γ.1 ∧
     h (x.1 + α.1) + d (x.1 + α.1) * (x.2 + α.2 + ApnCipherC7.star e x.1 α.1)
       = h x.1 + d x.1 * x.2 + γ.2 + ApnCipherC7.star e (p x.1) γ.1) :=
  Prod.ext_iff

/-- γ with low digit 0: rows with u ≠ 0 contribute nothing (p a permutation). -/
theorem colF_low0_nonZ {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F)
    (hp : Function.Injective p) (u v : F) (hu : u ≠ 0) (γ : F × F) (hγ : γ.1 = 0) :
    ddtC (ApnCipherC7.star e) (pdF p h d) (u, v) γ = 0 := by
  unfold ddtC
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have hx' := (memF e p h d x _ _).1 hx
  dsimp only at hx'
  obtain ⟨e1, -⟩ := hx'
  rw [hγ, add_zero] at e1
  have h1 := hp e1
  exact hu (by linear_combination h1)

/-- Z rows of F: Σ_v ddtC((0, v), γ) ≤ N for every γ (the second digit fixes v given x). -/
theorem colF_Z {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (γ : F × F) :
    ∑ v, ddtC (ApnCipherC7.star e) (pdF p h d) ((0 : F), v) γ ≤ Fintype.card F * Fintype.card F := by
  have h := (show ∑ v, ddtC (ApnCipherC7.star e) (pdF p h d) ((0 : F), v) γ ≤ (univ : Finset (F × F)).card by
    unfold ddtC
    refine sum_card_filter_le (fun v x => pdF p h d (cadd (ApnCipherC7.star e) x ((0 : F), v))
      = cadd (ApnCipherC7.star e) (pdF p h d x) γ) univ (fun _ _ _ => mem_univ _) ?_
    intro v v' x hx hx'
    have h1 := (memF e p h d x _ _).1 hx
    have h2 := (memF e p h d x _ _).1 hx'
    dsimp only at h1 h2
    obtain ⟨-, e2⟩ := h1
    obtain ⟨-, e2'⟩ := h2
    simp only [add_zero, star_zero_right] at e2 e2'
    have : d x.1 * v = d x.1 * v' := by linear_combination e2 - e2'
    exact mul_left_cancel₀ (hd0 x.1) this)
  rw [card_univ, Fintype.card_prod] at h
  exact h

/-- γ with low digit ≠ 0: Z rows (and the zero row) contribute nothing. -/
theorem colF_lowne_Z {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (v : F)
    (γ : F × F) (hγ : γ.1 ≠ 0) :
    ddtC (ApnCipherC7.star e) (pdF p h d) ((0 : F), v) γ = 0 := by
  unfold ddtC
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have hx' := (memF e p h d x _ _).1 hx
  dsimp only at hx'
  obtain ⟨e1, -⟩ := hx'
  rw [add_zero] at e1
  exact hγ (by linear_combination -e1)

/-- E rows of F: Σ_v ddtC((ρ, v), γ) ≤ 2q (at most two a by APN along ρ, one v per x). -/
theorem colF_E {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (hd0 : ∀ a, d a ≠ 0)
    (ρ : F) (hapn : ∀ a a', p (a + ρ) - p a = p (a' + ρ) - p a' → a' = a ∨ a' = a + ρ)
    (γ : F × F) :
    ∑ v, ddtC (ApnCipherC7.star e) (pdF p h d) (ρ, v) γ ≤ 2 * Fintype.card F := by
  set A := univ.filter (fun a => p (a + ρ) - p a = γ.1) with hA
  have hsum : ∑ v, ddtC (ApnCipherC7.star e) (pdF p h d) (ρ, v) γ ≤ (A ×ˢ (univ : Finset F)).card := by
    unfold ddtC
    refine sum_card_filter_le (fun v x => pdF p h d (cadd (ApnCipherC7.star e) x (ρ, v))
      = cadd (ApnCipherC7.star e) (pdF p h d x) γ) _ ?_ ?_
    · intro v x hx
      have hx' := (memF e p h d x _ _).1 hx
      dsimp only at hx'
      obtain ⟨e1, -⟩ := hx'
      rw [mem_product, hA, mem_filter]
      exact ⟨⟨mem_univ _, by linear_combination e1⟩, mem_univ _⟩
    · intro v v' x hx hx'
      have h1 := (memF e p h d x _ _).1 hx
      have h2 := (memF e p h d x _ _).1 hx'
      dsimp only at h1 h2
      obtain ⟨-, e2⟩ := h1
      obtain ⟨-, e2'⟩ := h2
      have : d (x.1 + ρ) * v = d (x.1 + ρ) * v' := by linear_combination e2 - e2'
      exact mul_left_cancel₀ (hd0 _) this
  rw [card_product, card_univ] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ (apn_fiber_le p ρ hapn γ.1))

/-- G rows of F: entry ≤ 2 (K(u) ≠ 0 fixes b per a; APN along u). -/
theorem entF_G {m : ℕ} (e : F ≃+ (Fin m → ZMod 2)) (p h d : F → F) (u v k : F)
    (hk : k ≠ 0) (hd : ∀ a, d (a + u) = d a + k)
    (hapn : ∀ a a', p (a + u) - p a = p (a' + u) - p a' → a' = a ∨ a' = a + u) (γ : F × F) :
    ddtC (ApnCipherC7.star e) (pdF p h d) (u, v) γ ≤ 2 := by
  unfold ddtC
  set S := univ.filter (fun x => pdF p h d (cadd (ApnCipherC7.star e) x (u, v))
      = cadd (ApnCipherC7.star e) (pdF p h d x) γ) with hS
  have hinj : Set.InjOn Prod.fst (S : Set (F × F)) := by
    intro x hx y hy hxy
    replace hx := (mem_filter.mp (mem_coe.mp hx)).2
    replace hy := (mem_filter.mp (mem_coe.mp hy)).2
    have h1 := (memF e p h d x _ _).1 hx
    have h2 := (memF e p h d y _ _).1 hy
    dsimp only at h1 h2
    obtain ⟨-, e2⟩ := h1
    obtain ⟨-, e2'⟩ := h2
    have hxy' : x.1 = y.1 := hxy
    rw [← hxy'] at e2'
    have hkb : k * x.2 = k * y.2 := by
      linear_combination e2 - e2' - (x.2 - y.2) * hd x.1
    exact Prod.ext hxy' (mul_left_cancel₀ hk hkb)
  have hmaps : Set.MapsTo Prod.fst (S : Set (F × F))
      ((univ.filter (fun a => p (a + u) - p a = γ.1) : Finset F) : Set F) := by
    intro x hx
    replace hx := (mem_filter.mp (mem_coe.mp hx)).2
    have hx' := (memF e p h d x _ _).1 hx
    dsimp only at hx'
    obtain ⟨e1, -⟩ := hx'
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, by linear_combination e1⟩
  exact (card_le_card_of_injOn _ hmaps hinj).trans (apn_fiber_le p u hapn γ.1)

/-! ### generic facts -/

/-- every DDT row (carry group) has total ≤ |F × F| (each x has exactly one output difference). -/
theorem rowsum_le (c : F → F → F) (f : F × F → F × F) (α : F × F) :
    ∑ β, ddtC c f α β ≤ Fintype.card (F × F) := by
  rw [← card_univ]
  unfold ddtC
  refine sum_card_filter_le (fun β x => f (cadd c x α) = cadd c (f x) β) univ
    (fun _ _ _ => mem_univ _) ?_
  intro β β' x hx hx'
  have H : cadd c (f x) β = cadd c (f x) β' := hx.symm.trans hx'
  have h1 : β.1 = β'.1 := by
    have := congrArg Prod.fst H
    simp only [cadd] at this
    linear_combination this
  have h2 : β.2 = β'.2 := by
    have := congrArg Prod.snd H
    simp only [cadd] at this
    rw [h1] at this
    linear_combination this
  exact Prod.ext h1 h2

/-- an injective map has no transition from α ≠ 0 to 0 (when c y 0 = 0). -/
theorem ddtC_to_zero (c : F → F → F) (hc0 : ∀ y, c y 0 = 0) (f : F × F → F × F)
    (hf : Function.Injective f) (α : F × F) (hα : α ≠ 0) :
    ddtC c f α 0 = 0 := by
  unfold ddtC
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have hz : cadd c (f x) 0 = f x := by
    simp only [cadd, Prod.fst_zero, Prod.snd_zero, add_zero, hc0, Prod.mk.eta]
  rw [hz] at hx
  have H := hf hx
  have h1 : α.1 = 0 := by
    have := congrArg Prod.fst H
    simp only [cadd] at this
    linear_combination this
  have h2 : α.2 = 0 := by
    have := congrArg Prod.snd H
    simp only [cadd, h1, hc0, add_zero] at this
    linear_combination this
  exact hα (Prod.ext h1 h2)

theorem pdB_injective (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    Function.Injective (pdB p h d) := by
  intro x y hxy
  have e1 := congrArg Prod.fst hxy
  have e2 := congrArg Prod.snd hxy
  simp only [pdB] at e1 e2
  have h1 : x.1 = y.1 := hp e2
  rw [h1] at e1
  have : d y.1 * x.2 = d y.1 * y.2 := by linear_combination e1
  exact Prod.ext h1 (mul_left_cancel₀ (hd0 _) this)

theorem pdF_injective (p h d : F → F) (hp : Function.Injective p) (hd0 : ∀ a, d a ≠ 0) :
    Function.Injective (pdF p h d) := by
  intro x y hxy
  have e1 := congrArg Prod.fst hxy
  have e2 := congrArg Prod.snd hxy
  simp only [pdF] at e1 e2
  have h1 : x.1 = y.1 := hp e1
  rw [h1] at e2
  have : d y.1 * x.2 = d y.1 * y.2 := by linear_combination e2
  exact Prod.ext h1 (mul_left_cancel₀ (hd0 _) this)

end ApnCipherC8

end
