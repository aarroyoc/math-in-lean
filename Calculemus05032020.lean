-- https://www.glc.us.es/~jalonso/calculemus/el-problema-logico-del-mal/

open Classical

theorem modus_tollens 
    {P Q : Prop}
    (p : P → Q)
    (q : ¬ Q)
  : ¬P := by
  intro h
  apply q
  apply p
  exact h

theorem not_not_intro {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : ¬ p => hn h

theorem of_not_not [Decidable p] : ¬ ¬ p → p :=
  fun hnn => byContradiction (fun hn => absurd hn hnn)

-- a : Dios es capaz de evitar el mal
-- b : Dios quiere evitar el mal
-- c : Dios evita el mal
-- d : Dios es omnipotente
-- e : Dios es malévolo
-- f : Dios existe

theorem god_exists_1 (a b c d e f : Prop)
    (h1 : (a ∧ b) → c)
    (h2 : ¬ a → ¬ d)
    (h3 : ¬ b → e)
    (h4 : ¬ c)
    (h5 : f → (d ∧ ¬ e))
 : ¬f := by
  intro h
  have h6 := h5 h
  have h7 := And.left h6
  have h8 := And.right h6
  have h9 := modus_tollens h3 h8
  have h10 := mt h2 (not_not_intro h7)
  have h11 := of_not_not h10
  have h12 := of_not_not h9
  have h13 := And.intro h11 h12
  have h14 := h1 h13
  apply absurd h14 h4
