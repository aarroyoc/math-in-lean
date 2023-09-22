open Classical

#check Prop
#check Nat
#check Type
#check And

variable (p q : Prop)

-- commutativity of ∧ and ∨ 
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro 
      (fun h : p ∧ q =>
       show q ∧ p from And.intro (And.right h) (And.left h))
      (fun h : q ∧ p =>
       show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h  

theorem or_swap : p ∨ q ↔ q ∨ p :=
  Iff.intro 
    (fun h : p ∨ q =>
      match h with
        | Or.inl hp => Or.inr hp
        | Or.inr hq => Or.inl hq)
    (fun h : q ∨ p =>
      match h with
        | Or.inl hq => Or.inr hq
        | Or.inr hp => Or.inl hp)

#check or_swap p q