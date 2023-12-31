open Nat

theorem sum_associativity (a b c : Nat) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rw [Nat.add_zero]
    rw [Nat.add_zero]
  | succ n ih =>
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [ih]