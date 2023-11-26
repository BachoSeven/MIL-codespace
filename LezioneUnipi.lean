import Mathlib

example (n:ℕ) : (n=0) ∨ (∃ (m:ℕ), Nat.succ m = n) := by
  induction n with
  | zero =>
    left
    trivial
  | succ n _ =>
    right
    use n

-- `contrapose` fa automaticamente push_neg
-- `tauto` fa "letteralmente" una tabella di verità
-- `decide` è simile, controlla i casi possibili

-- Tipi Induttivi

inductive MyNat
  | zero: MyNat
  | succ: MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

theorem add_zero (x: MyNat) : add x zero = x :=
  rfl

example (x: MyNat) : add x zero = x :=
  add_zero x

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

def pow : MyNat → MyNat → MyNat
  | _, zero => succ zero
  | x, succ y => mul (pow x y) x

def fac : MyNat → MyNat
  | zero => succ zero
  | succ n => mul (succ n) (fac n)

example : fac zero = succ zero := by
  rw [fac]

-- Finite Sets
open Finset
open BigOperators
#reduce range 4

-- induzione su insiemi finiti (per dimostrare che P vale ∀s insieme finito)
example {s: Finset ℕ} {p: ℕ} (prime_p : p.Prime) : (∀ n∈s, Nat.Prime n) → (p ∣ ∏n in s, n) → p∈s := by
  intros h₁ h₂
  induction s using Finset.induction with
  | _ => sorry

-- somme/prodotti a supporto finito
open Finsupp
#check Finsupp.sum

-- "congruenze"
example (a x x' y y' : ℕ) (hx : x≤x') (hy: y≤y') : a*x+y≤a*x'+y' := by
  gcongr

-- "Utopia": cercano nella libreria di Mathlib "il teorema giusto"
example : 1≠0 := by
  -- apply?
  exact Nat.one_ne_zero
  -- exact? -- un po' più restrittivo

-- norm_num FA I CONTI
