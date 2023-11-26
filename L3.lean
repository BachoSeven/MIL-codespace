inductive Formula where
  | var : Nat → Formula
  | neg : Formula → Formula
  | implies : Formula → Formula → Formula

open Formula

-- per la leggibilità, i numeri indicano la priorità
notation:60 "|" x "|" => var x
notation:65 "~ " x:55 => neg x
infixr:50 " → " => implies

#check implies (neg (var 5)) (var 6)
#check ~|5| → |6|

-- v è una interpretazione delle variabili
def eval (v : Nat → Bool) : Formula → Bool
  | var n => v n
  | neg φ => ¬ (eval v φ)
  | implies α β => (eval v α  ) → (eval v β )

#reduce eval (fun x => if Nat.mod x 2 = 0 then true else false) (|5| → |4|)

def valid (φ : Formula) : Prop :=
  ∀ v : Nat → Bool, eval v φ = true

example : valid ((|0| → |1| → ~|2| → ~|3|) →  |3| → |0| → |1| → |2|) := by
  rw [valid]
  intro v
  repeat rw [eval]
  cases v 0
  all_goals cases v 1
  all_goals cases v 2
  all_goals cases v 3
  all_goals rfl

def axiom1 (α β : Formula) := α → β → α
def axiom2 (α β γ : Formula) := (α → β → γ) → (α → β) → α → γ
def axiom3 (α β : Formula) := (~α → ~β) → (~α → β) → α

-- definiamo una famiglia di tipi "deducibili"
inductive derivable : Formula → Prop where
  | ax1 : (α β : Formula) → derivable (axiom1 α β)
  | ax2 : (α β γ : Formula) → derivable (axiom2 α β γ)
  | ax3 : (α β : Formula) → derivable (axiom3 α β)
  -- {...} dice a Lean che deve inferire da solo chi siano α e β senza che glielo dica
  | mp : {α β : Formula} → derivable (α → β) → derivable α → derivable β

open derivable

theorem pippo : derivable (|0| → |0|) := by
  have l1 : ∀ β, derivable ((|0| → β → |0|) → (|0| → β) → (|0| → |0|)) := by
    intro β
    exact ax2 (|0|) β (|0|)
  have l2 : ∀ β, derivable ((|0| → β) → (|0| → |0|)) := by
    intro β
    exact mp (l1 β) (ax1 (|0|) β)
  have l3 : derivable (|0| → (|0| → |0|)) :=
    ax1 (|0|) (|0|)
  exact mp (l2 (|0| → |0|)) l3

-- qui lo sta facendo da solo
#reduce pippo
-- OUTPUT: mp (mp (ax2 (|0|) (|0| → |0|) (|0|)) (ax1 (|0|) (|0| → |0|))) (ax1 (|0|) (|0|))

-- Correttezza: derivabile → valida
theorem soundness {φ : Formula} (h : derivable φ) : valid φ := by
  induction h with
  | ax1 => sorry
  | ax2 => sorry
  | ax3 => sorry
  | mp => sorry

theorem ax1_valid {α β : Formula} : valid (axiom1 α β) := by
  rw [valid]
  intro v
  rw [axiom1]
  repeat rw [eval]
  all_goals cases eval v α
  all_goals cases eval v β
  all_goals rfl

theorem ax2_valid {α β γ : Formula} : valid (axiom2 α β γ) := by
  rw [valid]
  intro v
  rw [axiom2]
  repeat rw [eval]
  all_goals cases eval v α
  all_goals cases eval v β
  all_goals cases eval v γ
  all_goals rfl

theorem ax3_valid {α β : Formula} : valid (axiom3 α β) := by
  rw [valid]
  intro v
  rw [axiom3]
  repeat rw [eval]
  all_goals cases eval v α
  all_goals cases eval v β
  all_goals rfl


theorem modus_ponens {α β : Formula} : valid (α → β) → valid α → valid β := by
  repeat rw [valid]
  intros hi ha v
  repeat rw [eval]
  have hiv := hi v
  have hav := ha v
  all_goals rw [eval] at hiv
  all_goals cases eval v α
  all_goals simp [hav] at hiv
  all_goals exact hiv