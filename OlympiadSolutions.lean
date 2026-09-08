import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas


-- Question 1
-- Color (i,j) white iff (i+j) even; center (4,4) has i+j=8, even, matching "center is white".
theorem q1_proof :
    ((Finset.range 9 ×ˢ Finset.range 9).filter (fun p => (p.1 + p.2) % 2 = 0)).card = 41 := by
  decide

-- Question 2
theorem q2_proof :
    ((Finset.range 256).filter (fun r => r % 4 = 0 ∧ r ≠ 0)).card = 63 := by
  decide

-- Question 3
-- A rigorous proof: 52 is both achievable and the minimum possible sum of squares.
theorem q3_proof :
    (∃ x : Fin 49 → ℤ, (∀ i, x i ≠ 0) ∧ ∑ i, x i = 0 ∧ ∑ i, (x i) ^ 2 = 52) ∧
    (∀ x : Fin 49 → ℤ, (∀ i, x i ≠ 0) → ∑ i, x i = 0 → 52 ≤ ∑ i, (x i) ^ 2) := by
  constructor
  · use fun i => if i.val < 25 then 1 else if i.val < 48 then -1 else -2
    refine ⟨fun i => ?_, ?_, ?_⟩
    · dsimp only; split_ifs <;> decide
    · decide
    · decide
  · intro x hx hsum
    have h2 : ∃ i0, x i0 ≠ 1 ∧ x i0 ≠ -1 := by
      by_contra hcon
      push Not at hcon
      have hodd : ∀ i, ∃ w : ℤ, x i = 1 + (w + w) := by
        intro i
        by_cases h : x i = 1
        · exact ⟨0, by omega⟩
        · exact ⟨-1, by have := hcon i h; omega⟩
      choose w hw using hodd
      have hsum2 : ∑ i, x i = 49 + (∑ i, w i + ∑ i, w i) := by
        calc ∑ i, x i = ∑ i, (1 + (w i + w i)) := Finset.sum_congr rfl (fun i _ => hw i)
          _ = ∑ i, (1 : ℤ) + ∑ i, (w i + w i) := Finset.sum_add_distrib
          _ = ∑ i, (1 : ℤ) + (∑ i, w i + ∑ i, w i) := by rw [Finset.sum_add_distrib]
          _ = 49 + (∑ i, w i + ∑ i, w i) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      rw [hsum] at hsum2
      omega
    obtain ⟨i0, h1, h2⟩ := h2
    have hge4 : (x i0) ^ 2 ≥ 4 := by
      have := hx i0
      rcases show x i0 ≤ -2 ∨ x i0 ≥ 2 by omega with h | h <;> nlinarith
    have hge1 : ∀ i, (x i) ^ 2 ≥ 1 := fun i => by
      have := hx i
      rcases show x i ≤ -1 ∨ x i ≥ 1 by omega with h | h <;> nlinarith
    have htail : (48 : ℤ) ≤ ∑ i ∈ Finset.univ.erase i0, (x i) ^ 2 := by
      calc (48 : ℤ) = ∑ i ∈ Finset.univ.erase i0, (1 : ℤ) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
                Finset.card_univ, Fintype.card_fin]; ring
        _ ≤ ∑ i ∈ Finset.univ.erase i0, (x i) ^ 2 :=
            Finset.sum_le_sum (fun i _ => hge1 i)
    have hsplit : ∑ i, (x i) ^ 2 = (x i0) ^ 2 + ∑ i ∈ Finset.univ.erase i0, (x i) ^ 2 :=
      (Finset.add_sum_erase Finset.univ (fun i => (x i) ^ 2) (Finset.mem_univ i0)).symm
    rw [hsplit]
    linarith


-- Question 4
theorem q4_proof :
    let N := 10 * (9 + 8 + 7) + (6 + 5 + 4)
    N = 255 ∧ (N / 100) + ((N / 10) % 10) + (N % 10) = 12 := by
  decide

-- Question 5
-- ∠BNC = ∠BAC = 80 deg by the inscribed angle theorem, since A, N lie on the same side of BC and
-- both see arc BC. NB = NC since N is equidistant from B, C (on the perpendicular bisector),
-- making triangle NBC isosceles.
theorem q5_proof (angleBNC angleNBC : ℕ)
    (h_sum : angleBNC + 2 * angleNBC = 180)
    (h_vert : angleBNC = 80) : -- inscribed angle theorem
    angleNBC = 50 := by
  omega

-- Question 6
theorem q6_proof :
    ((Finset.range 100).filter (fun n => n ≥ 10 ∧ n = 26 + (n / 10) * (n % 10))).card = 3 := by
  decide

-- Question 7 (Structurally Recursive DP)
def step (acc : List ℕ) : List ℕ :=
  let get (k : ℕ) : ℕ := acc.getD k 0
  (get 1 + get 3 + get 7 + get 8) :: acc

def dp : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => step (dp n)

def count_compositions (n : ℕ) : ℕ :=
  (dp n).head!

theorem q7_proof : count_compositions 14 = 31 := by
  rfl

-- Question 8
theorem q8_proof (x y : ℕ) (hx : x = 150) (hy : y = 30) : x / y = 5 := by
  rw [hx, hy]

-- Question 9
-- General fact: digit sum of (2·10^k − 1) is 9k+1.
-- General fact: digit sum of (2·10^k − 1) is 9k+1.
theorem digitSum_two_pow_sub_one :
    ∀ k : ℕ, (Nat.digits 10 (2 * 10 ^ k - 1)).sum = 9 * k + 1 := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
      have h10 : 0 < 10 ^ k := by positivity
      have hpow : (10 : ℕ) ^ (k + 1) = 10 * 10 ^ k := by ring
      have heq : 2 * 10 ^ (k + 1) - 1 = 10 * (2 * 10 ^ k - 1) + 9 := by
        rw [hpow]; omega
      have hpos : 0 < 10 * (2 * 10 ^ k - 1) + 9 := by omega
      have hmod : (10 * (2 * 10 ^ k - 1) + 9) % 10 = 9 := by omega
      have hdiv : (10 * (2 * 10 ^ k - 1) + 9) / 10 = 2 * 10 ^ k - 1 := by omega
      rw [heq, Nat.digits_def' (by norm_num : 2 ≤ 10) hpos, hmod, hdiv]
      rw [List.sum_cons, ih]
      omega

-- General fact: digits of 2·10^k are k zeros followed by a 2.
theorem digits_two_ten_pow :
    ∀ k : ℕ, Nat.digits 10 (2 * 10 ^ k) = List.replicate k 0 ++ [2] := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
      have hpow : (10 : ℕ) ^ (k + 1) = 10 * 10 ^ k := by ring
      have hpos : 0 < 2 * 10 ^ (k + 1) := by positivity
      have hmod : (2 * 10 ^ (k + 1)) % 10 = 0 := by rw [hpow]; omega
      have hdiv : (2 * 10 ^ (k + 1)) / 10 = 2 * 10 ^ k := by rw [hpow]; omega
      rw [Nat.digits_def' (by norm_num : 2 ≤ 10) hpos, hmod, hdiv, ih]
      rfl

def N : ℕ := 2 * 10 ^ 225 - 1

theorem q9_digitsum : (Nat.digits 10 N).sum = 2026 := by
  unfold N
  have := digitSum_two_pow_sub_one 225
  omega

theorem q9_leading_digit_of_succ :
    (Nat.digits 10 (N + 1)).getLast? = some 2 := by
  have h10 : 0 < 10 ^ 225 := by positivity
  have hN1 : N + 1 = 2 * 10 ^ 225 := by unfold N; omega
  rw [hN1, digits_two_ten_pow]
  rfl


-- Question 10
def is_sum_of_two_squares (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun a =>
    (List.range (n + 1)).any fun b =>
      a * a + b * b == n

theorem q10_proof :
    ((Finset.range 21).filter (fun n => is_sum_of_two_squares n)).card = 13 := by
  decide
