/-
P3-02 (C3, Claude 2026-10-10): warm start of the Theorem-S recurrence.  Arithmetic part only.
Variable x = 1/q (x^2 = 1/N), omega = 2.  Same one-step map as C2's ThreeOverN (re-declared here, unchanged):
  step (z, e) = (2x^2 + 2x e,  4x^2 + z/2 + 2x e),    final(z, e) = max z (2x^2 + 2x e).
Warm start (C2 theorem E: every entry of T_B(alpha, .) is <= 1/q): the state after the FIRST B is bounded by (x, x).
seqW n is the state after n+1 B's, so boundW x n bounds EDP_{n+1}  (EDP_t: t B's then F).
Proved for 0 < x <= 1/32:
  * edp2_of_init : ANY initial pair (z, e) with z <= x, e <= x gives final(step(z,e)) <= 4 x^2   (link "entries <= 1/q")
  * boundW 1 <= 4 x^2,  boundW 2 <= (27/8) x^2,  boundW 3 <= (315/128) x^2,  boundW 4 <= (4883/2048) x^2
  * seqW is componentwise non-increasing, hence boundW n <= (4883/2048) x^2 for n >= 4  (t >= 5)
  * q-form: for real q >= 32, boundW (1/q) 1 <= 4 / q^2.
The link "EDP_t <= this bound" for the concrete Galois ring is on paper (C1 theorem S + C2 theorem E), not formalized here.
-/
import Mathlib

noncomputable section

namespace ApnCipherC3

/-- one step of the Theorem-S recurrence (pair = (z, e)), identical to ApnCipherC2.step. -/
def step (x : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * x ^ 2 + 2 * x * p.2, 4 * x ^ 2 + p.1 / 2 + 2 * x * p.2)

/-- final layer F of Theorem S. -/
def final (x : ℝ) (p : ℝ × ℝ) : ℝ := max p.1 (2 * x ^ 2 + 2 * x * p.2)

/-- warm-started sequence: seqW x n = state after n+1 B's, starting from (x, x). -/
def seqW (x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x, x)
  | n + 1 => step x (seqW x n)

def boundW (x : ℝ) (n : ℕ) : ℝ := final x (seqW x n)

lemma step_mono {x : ℝ} (hx : 0 ≤ x) {p p' : ℝ × ℝ} (h1 : p.1 ≤ p'.1) (h2 : p.2 ≤ p'.2) :
    (step x p).1 ≤ (step x p').1 ∧ (step x p).2 ≤ (step x p').2 := by
  have h3 : 2 * x * p.2 ≤ 2 * x * p'.2 := mul_le_mul_of_nonneg_left h2 (by linarith)
  simp only [step]
  constructor <;> linarith

lemma final_mono {x : ℝ} (hx : 0 ≤ x) {p p' : ℝ × ℝ} (h1 : p.1 ≤ p'.1) (h2 : p.2 ≤ p'.2) :
    final x p ≤ final x p' := by
  have h3 : 2 * x * p.2 ≤ 2 * x * p'.2 := mul_le_mul_of_nonneg_left h2 (by linarith)
  unfold final
  exact max_le_max h1 (by linarith)

/-! closed forms -/

lemma seqW1 (x : ℝ) : seqW x 1 = (4 * x ^ 2, 6 * x ^ 2 + x / 2) := by
  simp only [seqW, step]; ext <;> ring

lemma seqW2 (x : ℝ) : seqW x 2 = (3 * x ^ 2 + 12 * x ^ 3, 7 * x ^ 2 + 12 * x ^ 3) := by
  simp only [seqW, step]; ext <;> ring

lemma seqW3 (x : ℝ) : seqW x 3 =
    (2 * x ^ 2 + 14 * x ^ 3 + 24 * x ^ 4, 11 * x ^ 2 / 2 + 20 * x ^ 3 + 24 * x ^ 4) := by
  simp only [seqW, step]; ext <;> ring

lemma seqW4 (x : ℝ) : seqW x 4 =
    (2 * x ^ 2 + 11 * x ^ 3 + 40 * x ^ 4 + 48 * x ^ 5, 5 * x ^ 2 + 18 * x ^ 3 + 52 * x ^ 4 + 48 * x ^ 5) := by
  simp only [seqW, step]; ext <;> ring

section bounds
variable {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 32)
include hx0 hx

lemma pw (k : ℕ) : x ^ k ≤ (1 / 32 : ℝ) ^ k := pow_le_pow_left₀ hx0.le hx k

/-- link from "every entry after the first B is ≤ 1/q" to the t = 2 bound. -/
theorem edp2_of_init (z e : ℝ) (hz : z ≤ x) (he : e ≤ x) :
    final x (step x (z, e)) ≤ 4 * x ^ 2 := by
  have hs := step_mono hx0.le (p := (z, e)) (p' := (x, x)) hz he
  have hf := final_mono hx0.le hs.1 hs.2
  refine hf.trans ?_
  have hxx : step x (x, x) = (4 * x ^ 2, 6 * x ^ 2 + x / 2) := by simp only [step]; ext <;> ring
  rw [hxx]; unfold final; simp only
  have p1 := pw hx0 hx 1
  apply max_le (le_refl _)
  have : 2 * x ^ 2 + 2 * x * (6 * x ^ 2 + x / 2) = x ^ 2 * (3 + 12 * x) := by ring
  rw [this]
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have : 3 + 12 * x ≤ 4 := by norm_num at p1; linarith
  nlinarith

theorem boundW1_le : boundW x 1 ≤ 4 * x ^ 2 := by
  have := edp2_of_init hx0 hx x x le_rfl le_rfl
  show final x (step x (x, x)) ≤ 4 * x ^ 2
  exact this

theorem boundW2_le : boundW x 2 ≤ (27 / 8) * x ^ 2 := by
  have p1 := pw hx0 hx 1; have p2 := pw hx0 hx 2
  have hx2 : 0 ≤ x ^ 2 := by positivity
  unfold boundW final; rw [seqW2]; simp only
  apply max_le
  · have : 3 + 12 * x ≤ 27 / 8 := by norm_num at p1; linarith
    nlinarith
  · have : 2 * x ^ 2 + 2 * x * (7 * x ^ 2 + 12 * x ^ 3) = x ^ 2 * (2 + 14 * x + 24 * x ^ 2) := by ring
    rw [this]
    have : 2 + 14 * x + 24 * x ^ 2 ≤ 27 / 8 := by norm_num at p1 p2; nlinarith
    nlinarith

theorem boundW3_le : boundW x 3 ≤ (315 / 128) * x ^ 2 := by
  have p1 := pw hx0 hx 1; have p2 := pw hx0 hx 2; have p3 := pw hx0 hx 3
  have hx2 : 0 ≤ x ^ 2 := by positivity
  unfold boundW final; rw [seqW3]; simp only
  apply max_le
  · have : 2 * x ^ 2 + 14 * x ^ 3 + 24 * x ^ 4 = x ^ 2 * (2 + 14 * x + 24 * x ^ 2) := by ring
    rw [this]
    have : 2 + 14 * x + 24 * x ^ 2 ≤ 315 / 128 := by norm_num at p1 p2; nlinarith
    nlinarith
  · have : 2 * x ^ 2 + 2 * x * (11 * x ^ 2 / 2 + 20 * x ^ 3 + 24 * x ^ 4)
        = x ^ 2 * (2 + 11 * x + 40 * x ^ 2 + 48 * x ^ 3) := by ring
    rw [this]
    have : 2 + 11 * x + 40 * x ^ 2 + 48 * x ^ 3 ≤ 315 / 128 := by norm_num at p1 p2 p3; nlinarith
    nlinarith

theorem boundW4_le : boundW x 4 ≤ (4883 / 2048) * x ^ 2 := by
  have p1 := pw hx0 hx 1; have p2 := pw hx0 hx 2; have p3 := pw hx0 hx 3; have p4 := pw hx0 hx 4
  have hx2 : 0 ≤ x ^ 2 := by positivity
  unfold boundW final; rw [seqW4]; simp only
  apply max_le
  · have : 2 * x ^ 2 + 11 * x ^ 3 + 40 * x ^ 4 + 48 * x ^ 5
        = x ^ 2 * (2 + 11 * x + 40 * x ^ 2 + 48 * x ^ 3) := by ring
    rw [this]
    have : 2 + 11 * x + 40 * x ^ 2 + 48 * x ^ 3 ≤ 4883 / 2048 := by norm_num at p1 p2 p3; nlinarith
    nlinarith
  · have : 2 * x ^ 2 + 2 * x * (5 * x ^ 2 + 18 * x ^ 3 + 52 * x ^ 4 + 48 * x ^ 5)
        = x ^ 2 * (2 + 10 * x + 36 * x ^ 2 + 104 * x ^ 3 + 96 * x ^ 4) := by ring
    rw [this]
    have : 2 + 10 * x + 36 * x ^ 2 + 104 * x ^ 3 + 96 * x ^ 4 ≤ 4883 / 2048 := by
      norm_num at p1 p2 p3 p4; nlinarith
    nlinarith

lemma seqW_succ_le (n : ℕ) :
    (seqW x (n + 1)).1 ≤ (seqW x n).1 ∧ (seqW x (n + 1)).2 ≤ (seqW x n).2 := by
  induction n with
  | zero =>
    show (seqW x 1).1 ≤ (seqW x 0).1 ∧ (seqW x 1).2 ≤ (seqW x 0).2
    rw [seqW1]; simp only [seqW]
    have p1 := pw hx0 hx 1
    norm_num at p1
    constructor <;> nlinarith
  | succ n ih => exact step_mono hx0.le ih.1 ih.2

lemma seqW_le_of_le (n k : ℕ) :
    (seqW x (n + k)).1 ≤ (seqW x n).1 ∧ (seqW x (n + k)).2 ≤ (seqW x n).2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := seqW_succ_le hx0 hx (n + k)
    rw [← add_assoc]
    exact ⟨h.1.trans ih.1, h.2.trans ih.2⟩

/-- t ≥ 5 (n ≥ 4): uniform constant 4883/2048. -/
theorem boundW_le_t5 (n : ℕ) (hn : 4 ≤ n) : boundW x n ≤ (4883 / 2048) * x ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := seqW_le_of_le hx0 hx 4 k
  exact (final_mono hx0.le h.1 h.2).trans (boundW4_le hx0 hx)

end bounds

/-- q-form of the t = 2 statement: EDP_2 ≤ 4/N with N = q^2, for every real q ≥ 32. -/
theorem edp2_le_four_div_N (q : ℝ) (hq : 32 ≤ q) : boundW (1 / q) 1 ≤ 4 / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < 1 / q := by positivity
  have hx : 1 / q ≤ 1 / 32 := one_div_le_one_div_of_le (by norm_num) hq
  have h := boundW1_le hx0 hx
  have : 4 * (1 / q) ^ 2 = 4 / q ^ 2 := by field_simp
  linarith [h, this.le, this.ge]

end ApnCipherC3

end
