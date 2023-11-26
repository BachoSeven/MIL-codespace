import Mathlib

example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  constructor
  intro a
  constructor
  exact a.2
  exact a.1
  intro b
  constructor
  exact b.2
  exact b.1

theorem mp (P Q : Prop) : P → ((P → Q) → Q) := by
  intros f g
  exact g f

theorem simplify (P Q : Prop) : (((P → Q) → Q) →Q) → (P → Q) := by
  intros f p
  have g := mp P Q p
  exact f g

/-
I prossimi due esercizi mostrano che la tripla negazione
è equivalente alla singola negazione
-/
example (P: Prop) : (¬P → ¬¬¬P) := by
  intro f
  exact mp _ _ f

/-
Questo può sembrare leggermente non banale, ma in realtà è un
caso particolare del teorema "simplify"
-/
example (P: Prop) : (¬¬¬P → ¬P) := by
  intro f
  exact simplify _ _ f

-- per il resto del file, a,b,c,d,e denotano variabili reali
open Real
variable (a b c d e : ℝ)

-- f, g sono funzioni da R in sé
variable (f g : ℝ → ℝ)

-- Definizione: una funzione è surgettiva se... è surgettiva.
def surjective {X Y : Type} (f : X → Y) := ∀ y, ∃ x, f x = y

/-
come noto, se una composizione di funzioni è surgettiva,
la funzione più esterna è surgettiva
-/
example (h : surjective (g ∘ f)) : surjective g := by
  intro z
  let ⟨x , h1 ⟩ := h z
  use (f x)
  exact h1

/-
Per questo esercizio è probabile che ad un certo punto vogliate
riscrivere (f composto g)(qualcosa) = f(g(qualcosa)). Potete usare
la tattica "dsimp" (semplificazione delle definizioni).
-/
example (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) := by
  intro z
  let ⟨y, h1 ⟩ := hg z
  let ⟨x, h2 ⟩ := hf y
  use x
  rw [←h2] at h1
  exact h1

lemma due_uno_uno : (2 : ℝ)  = 1+1 := by
  norm_num

/-
se non avete fatto il natural number game: per questo esercizio potreste
aver bisogno del lemma precedente (wow!) e dei teoremi mul_comm, add_mul,
one_mul. Potete verificare cosa siano questi teoremi scrivendo
#check nome_teorema.
-/
example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d := by
  rw [mul_comm] at hyp
  rw [hyp,hyp']
  rw [due_uno_uno]
  repeat rw [add_mul]
  rw [one_mul]

/-
qui sotto ci sono un po' di teoremi utili per manipolare
disuguaglianze e un esempio di applicazione
-/
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

/-
siccome "rw" è furbo, il prossimo esercizio si riesce a risolvere
anche senza invocare i teoremi sulle disuguaglianze. In ogni caso,
i teoremi qui sopra bastano certamente.
-/
example (x y : ℝ) (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  exact h₀
  contrapose! h₁
  rw [h₁]

/-
Per questo esercizio bastano "apply" e "exact", e in effetti anche solo
"apply". Con le tattiche che conoscete credo però che sia necessario
invocare alcuni dei teoremi sulle disuguaglianze che trovate qui sopra.
-/
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_of_lt_of_le h₁
  linarith
