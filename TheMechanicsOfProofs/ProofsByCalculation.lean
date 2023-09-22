-- https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html

import Mathlib.Data.Real.Basic

example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 := by
calc
  (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
  _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
  _ = 20 := by ring


example {a b c d e f : ℤ}
  (h1 : a*d = b*c)
  (h2 : c*f = d*e)
  : d*(a*f - b*e) = 0 := by
  calc
    d*(a*f - b*e) = d*a*f - d*b*e := by ring
    _ = (a*d)*f - d*b*e := by ring
    _ = (b*c)*f - d*b*e := by rw[h1]
    _ = b*c*f - (d*e)*b := by ring
    _ = b*c*f - (c*f)*b := by rw[h2]
    _ = 0 := by ring


example {x : ℤ}
  (h1 : x + 4 = 2)
  : x = -2 := by
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

example {x : ℤ}
  (h1 : 2 * x + 3 = x)
  : x = -3 := by
  calc
    x = (2*x + 3) - x - 3 := by ring
    _ = x -x -3 := by rw [h1]
    _ = -3 := by ring

-- Exercises

example {x y : ℝ}
  (h1 : x = 3)
  (h2 : y = 4 * x - 3)
  : y = 9 := by
  calc
    y = y := by ring
    _ = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by ring

example {a b : ℤ}
  (h : a - b = 0)
  : a = b := by
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw[h]
    _ = b := by ring

example {x y : ℤ}
  (h1 : x - 3 * y = 5)
  (h2 : y = 3)
  : x = 14 := by
  calc
    x = x + (x - 3 * y) - (x - 3 * y) := by ring
    _ = x + 5 - (x - 3 * y) := by rw[h1]
    _ = 5 + 3*y := by ring
    _ = 5 + 3*3 := by rw[h2]
    _ = 14 := by ring