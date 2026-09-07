import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

-- Question 1
theorem q1_proof (w_rows b_rows : ℕ) (hw : w_rows = 5) (hb : b_rows = 4) :
    w_rows * 5 + b_rows * 4 = 41 := by
  rw [hw, hb]

-- Question 2
theorem q2_proof :
    ((Finset.range 256).filter (fun r => r % 4 = 0 ∧ r ≠ 0)).card = 63 := by
  decide

-- Question 3
theorem q3_proof :
    (25 * (1 : Int) + 23 * (-1) + 1 * (-2) = 0) ∧
    (25 * (1 ^ 2 : Int) + 23 * ((-1) ^ 2) + 1 * ((-2) ^ 2) = 52) := by
  decide

-- Question 4
theorem q4_proof :
    let N := 10 * (9 + 8 + 7) + (6 + 5 + 4)
    N = 255 ∧ (N / 100) + ((N / 10) % 10) + (N % 10) = 12 := by
  decide

-- Question 5
theorem q5_proof (angleBNC angleNBC : ℕ)
    (h_sum : angleBNC + 2 * angleNBC = 180)
    (h_vert : angleBNC = 80) :
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
theorem q9_proof (k : ℕ) (hk : 10 ^ k > 0) : (2 * 10 ^ k) / 10 ^ k = 2 := by
  simp [hk]

-- Question 10
def is_sum_of_two_squares (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun a =>
    (List.range (n + 1)).any fun b =>
      a * a + b * b == n

theorem q10_proof :
    ((Finset.range 21).filter (fun n => is_sum_of_two_squares n)).card = 13 := by
  decide
