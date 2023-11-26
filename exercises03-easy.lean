/-
Consideriamo le formule proposizionali che contengono variabili,
implicazioni, e negazioni (questo e' un insieme completo di connettivi).
Diciamo che una formula e' valida se, per ogni assegnazione di valori di
verita' T/F alle variabili, il valore di verita' della formula e' T. Il
nostro scopo e' dimostrare il risultato seguente.

Teorema: una formula e' valida se e solo se e' deducibile dagli assiomi
  ax1  :  α → β → α
  ax2  :  (α → β → γ) → (α → β) → α → γ
  ax3  :  (~ α → ~ β) → (~ α → β) → α
con l'unica regola
  mp   :  α → β , α ⊢ β
dove, negli assiomi come nella regola mp (modus ponens), i simboli α β γ
rappresentano formule arbitrarie.

Nota: non usero' Mathlib, pero', se vuoi sfruttarla, puoi farlo!

Iniziamo dicendo che una formula puo' essere:
  var n         che rappresenta la variabile x_n
  neg φ         che rappresenta la formula "non φ"
  implies φ ψ   che rappresenta la formula "φ implica ψ"
-/

inductive Formula where
  | var : Nat → Formula
  | neg : Formula → Formula 
  | implies : Formula → Formula → Formula

open Formula

/-
Formula e' un tipo induttivo. In pratica un tipo induttivo contiene
oggetti che possono essere costruiti da dei "costruttori", nel nostro caso
(var n) (neg φ) (implies φ ψ) i quali possono prendere per argomento
oggetti di altri tipi (come var) o anche oggetti del tipo stesso (in
realta' il concetto e' piu' generale, ma per ora limitiamoci a questo).
L'esempio principe di tipo induttivo e' Nat, che potremmo definire
  inducive Nat where
    | zero : Nat
    | succ : Nat → Nat
per dire che un numero naturale o e' zero o e' (succ n) per qualche altro
numero naturale n. Hai fatto il natural numbers game, vero?

Scrivere cose tipo (implies (neg (var 2)) (implies (var 3) (var 1))) e'
scomodo. Meglio (~|2| → |3| → |1|). Definiamo questa notazione.

Non mi interessa che tu capisca veramente i comandi che seguono, comunque,
se ti interessa, puoi leggere come funzionano qui:
https://lean-lang.org/theorem_proving_in_lean4/interacting_with_lean.html#notation
-/

notation:60 "|" x "|" => var x
notation:55 "~ " x:55 => neg x
infixr:50 " → " => implies

-- Prova:
-- #check (implies (neg (var 2)) (implies (var 3) (var 1)))
-- #check ~|2| → |3| → |1|

/-
La funzione eval qua sotto prende una assegnazione v di valori di verita'
alle variabili, rappresentata da una funzione Nat → Bool, e una formula, e
calcola il valore di verita' della formula. Nota: v assegna un valore a
ogni variabile, non solo a quelle che compaiono nella formula.

def definisce una funzione, in questo caso per "ricorsione strutturale".
Ossia stiamo dicendo che una formula puo' essere di tre tipi
  var n
  neg n
  implies φ ψ
e, per ciascun tipo, spieghiamo a Lean4 come calcolare eval
-/

def eval (v : Nat → Bool) : Formula → Bool
  | var n => v n
  | neg φ => ¬ eval v φ
  | implies φ ψ => eval v φ → eval v ψ

-- Prova:
-- #reduce eval (fun x => if Nat.mod x 2 = 0 then true else false) (|2| → |7|)
-- #reduce eval (fun x => if Nat.mod x 2 = 0 then true else false) (|2| → |8|)
-- #reduce eval (fun x => if Nat.mod x 2 = 0 then true else false) (|3| → |7|)
-- #reduce eval (fun x => if Nat.mod x 2 = 0 then true else false) (|3| → |8|)

/-
Diciamo quindi che φ e' valida se il suo valore di verita' e' true per
qualunque assegnazione v di valori alle variabili.

Questo def, invece, rappresenta la sua funzione con un termine esplicito.
-/

def valid (φ : Formula) := ∀ v : Nat → Bool , eval v φ = true

/-
Come primo esempio, dimostriamo che la seguente formula e' valida.
-/

example : valid ((|0| → |1| → ~|2| → ~|3|) → |3| → |0| → |1| → |2|) := by
  -- dapprima espandiamo le definizioni
  rw [valid]
  intro v
  repeat rw [eval]
  -- ora dividiamo i casi secondo i valori di verita' di |0|, |1|, etc. 
  cases v 0
  all_goals cases v 1
  all_goals cases v 2
  all_goals cases v 3
  -- adesso tutti i casi non fanno che constatare dati di fatto
  all_goals rfl

example : valid ((~|0| → ~|1|) → (|1| → (|0| → |2|)) → (|0| → (|2| → ~|1|)) → |1| → |3|) := by
  sorry

/-
Ora descriviamo il sistema deduttivo. Rappresentiamo la deducibilita' per
mezzo di (indovina!) una famiglia di tipi induttivi. La riga
  inductive derivable : Formula → Prop where
nella definizione qua sotto, dice a Lean4 che derivable e' una famiglia di
tipi proposizione (diciamo di proposizioni) indicizzata sulle formule,
ossia e' un aggeggio che associa ad ogni formula una certa proposizione.
La famiglia ha quattro costruttori
  ax1 : (α β : Formula) → derivable (axiom1 α β)
  ax2 : (α β γ : Formula) → derivable (axiom2 α β γ)
  ax3 : (α β : Formula) → derivable (axiom3 α β)
  mp : {α β : Formula} → derivable (α → β) → derivable α → derivable β
Per esempio, il costruttore ax1 si usa passandogli due input α e β, il
risultato e' un oggetto di tipo
  derivable (axiom1 α β)
che, se guardiamo la definizione di axiom1, equivale a scrivere
  derivable (α → β → α)
In pratica, stiamo dicendo che chiamiamo (ax1 α β) un testimone del fatto
che (α → β → α) e' una formula deducibile (e' un assioma). Il costruttore
mp, facciamo finta, per un istante, che le parentesi graffe siano tonde,
ci dice che
  mp α β h1 h2    dove (h1 : derivable (α → β)) e (h2 : derivable α)
e' un testimone del fatto che β e' deducibile. Ossia, per testimoniare la
deducibilita' di β, per modus ponens, mi basta esibire un α, un testimone
del fatto che (α → β) e' deducibile, e un testimone del fatto che α e'
deducibile. Le parentesi graffe dicono a Lean4 che, siccome α e β si
possono desumere dal tipo di h1 e h2, noi scriveremo semplicemente
  mp (derivable (α → β)) (derivable α)
e sara' compito di Lean4 capire chi sono α e β e, dietro le quinte,
ricostuire l'espressione completa, come se la avessimo scritta noi.
-/

def axiom1 (α β : Formula) := α → β → α
def axiom2 (α β γ : Formula) := (α → β → γ) → (α → β) → α → γ
def axiom3 (α β : Formula) := (~ α → ~ β) → (~ α → β) → α

inductive derivable : Formula → Prop where
  | ax1 : (α β : Formula) → derivable (axiom1 α β)
  | ax2 : (α β γ : Formula) → derivable (axiom2 α β γ)
  | ax3 : (α β : Formula) → derivable (axiom3 α β)
  | mp : {α β : Formula} → derivable (α → β) → derivable α → derivable β

open derivable

/-
Questo arnese e' bastantemente scomodo. Come esempio dimostriamo x → x,
che scriviamo (|0| → |0|) -- ricordo che |0| e' la variabile x_0.
-/

example : derivable (|0| → |0|) := by
  -- sembra sensato partire da ax2 con α = γ = |0|, perche', al fondo,
  -- si ottiene |0| → |0|
  have h1 : ∀ β , derivable ((|0| → β → |0|) → (|0| → β) → |0| → |0|) :=
    fun β => ax2 (|0|) β (|0|)
  -- ora (|0| → β → |0|) e' un'istanza di ax1 quindi, per modus ponens
  have h2 : ∀ β , derivable ((|0| → β) → |0| → |0|) :=
    fun β => mp (h1 β) (ax1 (|0|) β)
  -- adesso ci basta trovare un qualunque β tale che |0| → β
  -- values of β will give rise to dom!
  have h3 : derivable (|0| → (|0| → |0|)) :=
    ax1 (|0|) (|0|)
  -- e finalmente ci siamo
  exact mp (h2 (|0| → |0|)) h3

/-
Se ci interessa, possiamo vedere il termine generato da questa
dimostrazione sostituendo "example" con "theorem pippo" e dando
  #reduce pippo
Cosi' scopriamo che, in un'unica fucilata, la dimostrazione e'
-/

example : derivable (|0| → |0|) :=
  mp (mp (ax2 (|0|) (|0| → |0|) (|0|)) (ax1 (|0|) (|0| → |0|))) (ax1 (|0|) (|0|))

/-
Pero' Lean4 e' abbastanza bravo a indovinare, per cui possiamo anche
scriverla nel modo seguente.
Domanda: perche' ho dovuto scrivere l'ultimo |0| esplicitamente?
Suggerimento: va bene anche |42|
-/

example : derivable (|0| → |0|) :=
  mp (mp (ax2 _ _ _) (ax1 _ _)) (ax1 _ (|0|))

/-
Per prima cosa, dimostriamo che tutte le formule che si ottengono come
istanze degli assiomi sono valide.
-/

theorem ax1_valid {α β : Formula} : valid (axiom1 α β) := by
  -- Procediamo esattamente come nell'esempio
  -- dapprima espandiamo le definizioni
  skip
  -- ora dividiamo i casi secondo i valori di verita' di α e β  
  skip
  -- adesso tutti i casi non fanno che constatare dati di fatto
  sorry

theorem ax2_valid {α β γ : Formula} : valid (axiom2 α β γ) := by
  sorry

theorem ax3_valid {α β : Formula} : valid (axiom3 α β) := by
  sorry

/-
Inoltre, se le premesse del mp sono valide, lo e' anche la conclusione
-/

theorem modus_ponens {α β : Formula} : valid (α → β) → valid α → valid β := by
  repeat rw [valid]
  intros hi ha v
  -- ricordati che puoi usare simp ... at ... per semplificare un'ipotesi
  sorry 

/-
A questo punto possiamo dimostrare la direzione facile del nostro
risultato, ossia che (derivable φ → valid φ). Questa dimostrazione procede
per induzione su derivable φ. Cosa vuol dire? Se pensiamo ai numeri
naturali, n : Nat puo' essere di due tipi
  0
  succ m
la classica induzione aritmetica ci dice che se mostriamo
  P 0                 che corrisponde a 0
  P m → P (succ m)    che corrisponde a succ m
allora abbiamo dimostrato (m : Nat) → P m
Ebbene, derivable φ puo' essere di quattro tipi
  ax1 α β  
  ax2 α β γ
  ax3 α β
  mp h1 h2    con (h1 : derivable α → β) e (h2 : derivable α)
Quindi se mostriamo
  P (ax1 α β)
  P (ax2 α β γ)
  P (ax3 α β)
  P h1 → P h2 → P (mp h1 h2)
abbiamo dimostrato (h : derivable φ) → P h
Ora dobbiamo semplicemente scrivere (valid φ) al posto di (P h)
Il risultato e' che dobbiamo verificare
  valid (α → β → α)
  valid ((α → β → γ) → (α → β) → α → γ)
  valid ((~ α → ~ β) → (~ α → β) → α)
  valid (α → β) → valid α → valid β

La dimostrazione e' molto leggibile. Nell'ultimo caso ih1 e ih2 sono le
ipotesi induttive
  ih1 : valid α β
  ih2 : valid α
Mentre i trattini dopo mp sono per gli argomenti
  derivable α β
  derivable α
che e' inutile assegnare a delle variabili perche' non li usiamo 
-/

theorem soundness {φ : Formula} (h : derivable φ) : valid φ := by
  induction h with
  | ax1 => exact ax1_valid
  | ax2 => exact ax2_valid
  | ax3 => exact ax3_valid
  | mp _ _ ih1 ih2 => exact modus_ponens ih1 ih2

/-
Se hai capito fin qua, ho raggiunto il mio scopo.

Ma adesso partiamo per la direzione difficle.

Nota: definiamo F come il falso, rappresentato da ~(|0| → |0|).
-/

def F : Formula := ~ (|0| → |0|) 

/-
Intanto avremo bisogno di dedurre a mano un po' di formule. Questa parte
e' nojosissima e poco istruttiva, per cui non perderci tempo. Quando ti
servira', per dire, che una formula del tipo (~ ~ α → α) e' deducibile,
potrai buttare l'occhio in questa sezione per cercare il nome del
risultato da invocare (in questo caso der_doub_neg).

Qui constatiamo semplicemente che certe formule particolari sono
deducibili: lascia perdere e passa alla parte interessante.
-/

--lax1 equivale a (ax1 _ _), etc.
def lax1 {α β : Formula} := ax1 α β

def lax2 {α β γ : Formula} := ax2 α β γ

def lax3 {α β : Formula} := ax3 α β

theorem der_add_hypot {α β γ : Formula} : derivable ((α → γ) → (α → β → γ)) :=
  mp lax2 (mp lax1 lax1)

theorem der_trans {α β γ : Formula} : derivable ((β → γ) → (α → β) → (α → γ)) :=
  mp (mp lax2 (mp lax1 lax2)) lax1

theorem der_id {α : Formula} : derivable (α → α) :=
  sorry

theorem der_swap {α β γ : Formula} : derivable ((α → β → γ) → (β → α → γ)) :=
  mp (mp lax2 (mp (mp lax2 (mp lax1 lax2))
          (mp (mp lax2 (mp lax1 lax1)) lax2))) (mp lax1 lax1)

theorem der_falsoex {α β : Formula} : derivable (α → ~ α → β) :=
  mp (mp der_trans (mp der_swap (mp (mp der_trans lax3) lax1))) lax1

theorem der_exfalso {α β : Formula} : derivable (~ α → α → β) :=
  mp der_swap der_falsoex

theorem der_afortiori : derivable (((α → β) → γ) → (β → γ)) :=
  mp (mp lax2 (mp (mp lax2 (mp lax1 lax2)) lax1)) (mp lax1 lax1)

theorem der_trap {α β : Formula}  : derivable ((~ α → β) → (~ β → α)) :=
  mp (mp der_trans der_afortiori) (mp der_swap lax3)

theorem der_doub_neg {α : Formula} : derivable (~ ~ α → α) :=
  mp der_trap der_id

theorem der_prem_of_not_implies {α β : Formula} : derivable (~ (α → β) → α) :=
  mp der_trap der_exfalso

theorem der_not_cons_of_not_implies {α β : Formula} : derivable (~ (α → β) → ~ β) :=
  mp der_trap (mp (mp der_trans lax1) der_doub_neg)

theorem der_add_doub_neg {α β : Formula} : derivable ((α → β) → (~ ~ α → β)) :=
  mp der_swap (mp (mp der_trans (mp der_swap der_id)) der_doub_neg)

theorem der_bycases {α β : Formula} : derivable ((~ α → β) → (α → β) → β) :=
  mp (mp der_trans (mp der_swap (mp (mp der_trans (mp (mp der_trans lax3) der_trap))
                                    der_add_doub_neg))) der_trap

theorem der_not_false : derivable (~ F) :=
  mp (mp lax3 der_doub_neg) (mp lax1 der_id)

theorem der_true_implies {α β γ : Formula} (h1 : derivable (~ α → γ)) (h2 : derivable (β → γ)) :
                                derivable ((α → β) → γ) :=
  have l1 : derivable   (α → (α → β) → γ) := mp der_swap (mp der_trans h2)
  have l2 : derivable (~ α → (α → β) → γ) := mp der_add_hypot h1
  mp (mp der_bycases l2) l1

theorem der_remove_false {α : Formula} (h1 : derivable (~ α → F)) : derivable α :=
  mp (mp der_trap h1) der_not_false

theorem der_parametric_bycases {α β γ : Formula}
                                (h1 : derivable (α → β → γ)) (h2 : derivable (α → ~ β → γ)) :
                                derivable (α → γ) :=
  have l1 : derivable (β → α → γ) := mp der_swap h1
  have l2 : derivable (~ β → α → γ) := mp der_swap h2
  mp (mp der_bycases l2) l1

/-
Questo e' il piano della dimostrazione. Ora sappiamo che tutte le righe
della tabella di verita' di una certa formula φ concludono che φ e' vera.
Per esempio
        x_0    x_1    x_2    x_3    ...     φ
        -------------------------------------
  r_0    V      V      V      V     ...     V
  r_1    F      V      V      V     ...     V
        ...
  r_v    V      F      F      V     ...     V
        ...
Vogliamo produrre una dimostrazione di φ. Spezziamo il problema in due
parti. Nella prima parte trasformiamo ogni riga della tabella in una
formula che asserisce la correttezza di quella riga, e dimostriamo che
questa formula e' deducibile. Per esempio la riga
        x_0    x_1    x_2    x_3    ...     φ
        -------------------------------------
  r_v    V      F      F      V     ...     V
diventa la formula
  φ_v = |0| → ~|1| → ~|2| →  |3| →  ...  →  φ 
Per dimostrare la deducibilita' di φ_v dovremo implementare, in qualche
modo, il meccanismo di calcolo della tavola di verita', per mezzo delle
regole di inferenza.

Nella seconda parte della dimostrazione, sfruttando il fatto che
  (α → β) → (~ α → β) → β
e' deducibile, potremo mettere insieme tutte le formule φ_v, ottenendo la
dimostrabilita' di φ.

In questo ho mentito. Le formule φ_v non saranno tipo
       ±|0| → ±|1| → ±|2| → ±|3| →  ...  →  φ 
bensi'
        ~φ  →  ... → ±|2| → ±|1| → ±|0|  →  F
Questa e' una formula equivalente, ma ha un vantaggio: scritta con le
parentesi ha l'aspetto
        ~φ  → (±|n| → ( roba ))
Quindi φ e la variabile |n|, ossia le due cose che vorremo manipolare nei
passi induttivi, sono direttamente accessibili, smontando il primo e il
secondo livello della formula. Usando, invece, la scrittura inziale, φ
sarebbe sepolta sotto n livelli di parentesi, e questo renderebbe
necessario il ricorso ad induzioni secondarie per accedervi (credetemi, ho
scritto anche questa dimostrazione). Lo svantaggio del nostro approccio e'
di richiedere un numero leggermente maggiore di formule dimostrate a mano
(pazienza, il grosso ve lo ho fornito io...).

Una nota circa la strategia dimostrativa. In un corso di logica, di
solito, si adotta un approccio piu' astratto. Ci sono diverse varianti,
ma, in sostanza, si dimostra che se φ non fosse deducibile, ~ φ sarebbe
coerente (nel senso che non implica l'assurdo). Dalla coerenza di ~ φ si
deduce l'esistenza di un modello, ossia un'assegnazione di valori alle
variabili che la rende vera, e questo e' un assurdo perche' tutte le
valutazioni delle variabili rendono, per ipotesi, vera φ. Questa
dimostrazione richiede di implementare (o importare da Mathlib) concetti
piu' astratti, ma non solo, ha anche un altro svantaggio: usa in modo
essenziale il principio del terzo escluso, non fornisce quindi un
algoritmo che permette di calcolare la dimostrazione di φ. A differenza
della nostra che e' formalizzata nel frammento intuizionistico di Lean4.

Cominciamo col definire le funzioni che generano le formule che
corrispondentono alle righe di una tabella di verita'. Siccome vogliamo
ragionare su queste cose per induzione, non possiamo limitarci alle righe
che finiscono in "φ e' vera", ma dobbiamo considerare entrambe le
possibilita' per il valore di verita' di φ. Quindi associamo alla riga
        x_0    x_1    x_2    x_3    ...     φ
        -------------------------------------
         V      F      F      V     ...   __V__
le formula
      __~φ__→  ... → ~|2| → ~|1| →  |0|  →  F
Mentre alla riga
        x_0    x_1    x_2    x_3    ...     φ
        -------------------------------------
         V      F      F      V     ...   __F__
le formula
       __φ__→  ... → ~|2| → ~|1| →  |0|  →  F
Questo e' realizzato dalle funzioni make_suffix, che prepara il suffisso
               ... → ~|2| → ~|1| →  |0|  →  F
e row_to_formula, che aggiunge (φ →) o (~φ →) a seconda del valore di
verita' di φ. Il codice si spiega da se'.
-/

def make_suffix (n : Nat) (v : Nat → Bool) : Formula :=
  match n with
  | 0 => F
  | m + 1 =>
    match v m with
    | true => |m| → make_suffix m v
    | false => ~ |m| → make_suffix m v

def row_to_formula (n : Nat) (v : Nat → Bool) (φ : Formula) : Formula :=
  (if eval v φ then ~ φ else φ) → (make_suffix n v)

-- Prova:
--#reduce row_to_formula 4 (fun x => if Nat.mod x 2 = 0 then true else false) (|1| → |2|)
--#reduce row_to_formula 4 (fun x => if Nat.mod x 2 = 0 then true else false) (|2| → |1|)

/-
Ora definiamo un predicato, variables_lt n φ, che dice che le variabili di
φ sono comprese fra le prime n, ossia che, se la variabile |x| compare in
φ, allora x < n. Ci servira' sapere che data una formula φ, esiste n tale
che (variables_lt n φ), e questo e' quello che dice il teorema
exists_variables_lt. Nella dimostrazione di exists_variables_lt, fara'
comodo il lemma variables_lt_monotonic, che dice che se m ≤ n, allora
(variables_lt m φ) → (variables_lt n φ) -- roba ovvia insomma. Entrambe le
dimostrazioni di questi risultati procedono per indizione su φ.

Induzione su φ? Beh, ormai hai capito che c'e' una ragione se si chiamano
tipi induttivi. φ puo' essere
  var n
  neg α
  implies α β
Quindi, per dimostrare (φ : Formula) → P φ, mi basta dimostrare che
  P (var n)
  P α → P (neg α)
  P α → P β → P (implies α β)
La possibilita' di fare questo e' automaticamente garantita dalla logica
di Lean4 nel momento in cui si definisce un tipo induttivo (e tutti i tipi
che non siano tipi freccia "A → B" o introdotti assiomaticamente sono tipi
induttivi).

Nota: nella dimostrazione di variables_lt_monotonic bisogna lavorare con
una disuguaglianza fra numeri naturali. Un risultato utile e'
  Nat.lt_of_lt_of_le
Il comando
  #check Nat.lt_of_lt_of_le
ci dice che
  Nta.lt_of_lt_of_le {n m k : Nat} (a✝ : n < m) (a✝¹ : m ≤ k) : n < k
Ossia Nat.lt_of_lt_of_le e'
  n < m  →  m ≤ k  →  n < k
Un'altro risultato che serve nella dimostrazione di exists_variables_lt
e' Nat.le_total
  Nat.le_total (m n : Nat) : m ≤ n ∨ n ≤ m
-/

def variables_lt (n : Nat) : Formula → Prop
  | var m => m < n
  | neg φ => variables_lt n φ
  | implies φ ψ => variables_lt n φ ∧ variables_lt n ψ 

/-
Le parentesi graffe in questo enunciato dicono a Lean4 che, quando lo
richiameremo, specificheremo solo le ipotesi h1 e h2, e non φ m n.
Possiamo farlo perche' φ m n sono impliciti in h1 e h2, quindi Lean4 e' in
grado di ricavarli.
-/

-- #check Nat.lt_of_lt_of_le

theorem variables_lt_monotonic  {φ : Formula} {m n : Nat} (h1 : m ≤ n)
                                (h2 : variables_lt m φ) : variables_lt n φ := by
  induction φ with
  | var p =>
    -- per vedere cosa effettivamente vuoi dimostrare, fai cosi'
    -- rw [variables_lt] at *
    sorry
  | neg ψ ih => sorry
  | implies α β ihα ihβ => sorry

-- #check Nat.lt_succ_self
-- #check Nat.le_total

theorem exists_variables_lt (φ : Formula) : ∃ n , variables_lt n φ := by
  induction φ with
  | var m =>
    -- la seguente non e' la scelta piu' elegante, pero' ti puo' aiutare
    -- simp [variables_lt]
    sorry
  | neg _ ih => sorry
  | implies α β ihα ihβ =>
    -- Nella riga seguente avrei potuto scrivere semplicemnete
    --   let ⟨ nα , ihα ⟩ := ihα
    -- Specificando il tipo di ihα rendo il codice piu' chiaro per te che
    -- lo stai leggendo: d'ora in poi ihα e' l'ipotesi che dice che vale
    -- variables_lt nα α (ossia e' un testimone di questa cosa).
    let ⟨ nα , (ihα : variables_lt nα α) ⟩ := ihα
    let ⟨ nβ , (ihβ : variables_lt nβ β) ⟩ := ihβ
    -- Nella riga seguente, Nat.le_total nα nβ e' (nα ≤ nβ ∨ nβ ≤ nα)
    have : nα ≤ nβ ∨ nβ ≤ nα := Nat.le_total nα nβ
    -- Ricorda: per dimostrare una disgiunzione: constructor
    --          per usare una disgiunzione: cases
    sorry

/-
Siamo giunti al main_lemma, che dice
  theorem main_lemma  {φ : Formula} {n : Nat}
                      (v : Nat → Bool) (h1 : variables_lt n φ) :
                      derivable (row_to_formula n v φ) := by
Ossia che e' deducibile la formula (row_to_formula n v φ) che rappresenta
la riga della tavola di verita' di φ corrispondente ai valori delle
variabili dati da v, a patto che il numero n delle variabili prese in
considerazione nella costruzione di (row_to_formula n v φ) sia abbastanza
grande (nella fattispecie soddisfi variables_lt n φ).

La dimostrazione procede per induzione su φ. Secondo che φ sia una
variabile, una negazione, o una implicazione, bisogna giustificare la
regola di calcolo corrispondente per mezzo di deduzioni nel nostro sistema
logico. Per esempio, se φ = ~ψ, e l'assegnazione v di valori alle
variabili rende ψ falsa, allora abbiamo l'ipotesi induttiva
  derivable ( ψ → suffisso )
e, siccome la tabella di verita' del ~ ci dice che, in questo caso, φ deve
essere vera, allora dobbiamo dimostrare
  derivable ( ~ φ → suffisso )
ossia
  derivable ( ~ ~ ψ → suffisso )
Potremo farlo perche' possiamo dedurre dagli assiomi che
  derivable ( ~ ~ α → α )
e che l'implicazione e' transitiva (in realta' abbiamo gia' dedotto questi
due fatterelli nella sezione che ti ho detto di saltare...).

Forse inaspettatamente, il caso piu' ostico e' proprio quando φ e' una
variabile, ossia quando, apparentemente, non ci sarebbe niente da fare. Il
guaio e' che se, per esempio, φ = |7| e v 7 = false, allora la formula da
dimostrare e'
  |7| →  ±|n| →  ±|n-1| →  ... →  ±|8| →  ~|7| →  ... →  ±|0| → F
che, ti ricordo, e' parentesizzata cosi'
  |7| → (±|n| → (±|n-1| → (... → (±|8| → (~|7| → (... → (±|0| → F) ... )
dove ho indicato con ± la possibilita' che ci sia o no una negazione.
E' chiaro che questa formula e' valida perche', se |7| e' vera, allora
~|7| e' falsa, quindi l'implicazione ~|7| → ... e' vera. Di conseguenza
anche l'implicazione ±|8| → (|7| → ...) e' vera, indipendentemente dal
valore di verita' di |8|. E si procede cosi' per tutta la catena. Pero'
formalizzare questo ragionamento richiede un'induzione su n, ho quindi
deciso di separare il caso φ = |n| facendone il lemma var_derivable.
-/

-- #check der_add_hypot
-- #check der_exfalso
-- #check der_falsoex
-- #check Nat.lt_or_ge
-- #check Nat.eq_or_lt_of_le
-- #check Nat.le_of_lt_succ
-- #check Nat.ne_of_lt
-- #check Nat.lt_of_le_of_lt

theorem var_derivable {m n : Nat} (v : Nat → Bool) (h1 : m < n) :
                      derivable (row_to_formula n v (|m|)) := by
  induction n with
  | zero =>
    -- m < 0 e' una contraddizione immediata
    sorry
  | succ p ih =>
    show derivable (row_to_formula (p + 1) v (|m|))
    have ih : m < p → derivable (row_to_formula p v (|m|)) := ih
    have h1 : m < p + 1 := h1
    -- Ora separiamo i casi m < p e m ≥ p. Uso cases su
    -- Nat.lt_or_ge m p : m < p ∨ m ≥ p
    cases (Nat.lt_or_ge m p : m < p ∨ m ≥ p) with
    | inl ch =>
      -- se m < p siamo in modalita' "procedo cosi' per tutta la catena"
      -- espandiamo le definizioni e usiamo l'ipotesi induttiva,
      -- sfruttando, per aggiungere un'implicazione alla catena, il fatto
      --   der_add_hypot : derivable ((α → γ) → (α → β → γ))
      sorry
    | inr ch =>
      -- se m ≥ p vogliamo dedurre che m = p
      cases (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h1) : m = p ∨ m < p) with
      -- Ok, questo delirio e' solo perche' non voglio importare Mathlib
      | inl ch2 =>
        -- siamo nel caso m = p
        rw [← ch2]
        sorry
      | inr ch2 =>
        -- il caso m < p e' chiaramente impossibile
        have := Nat.ne_of_lt (Nat.lt_of_le_of_lt ch ch2)
        contradiction

-- #check der_trans
-- #check der_doub_neg
-- #check der_prem_of_not_implies
-- #check der_not_cons_of_not_implies
-- #check der_true_implies

theorem main_lemma  {φ : Formula} {n : Nat}
                    (v : Nat → Bool) (h1 : variables_lt n φ) :
                    derivable (row_to_formula n v φ) := by
  induction φ with
  -- Se φ = |m|
  | var m =>
    show derivable (row_to_formula n v (|m|))
    have h2 : m < n := by
      sorry
    -- e questo e' il lemma
    sorry
  -- Se φ = ~ α
  | neg α ih =>
    show derivable (row_to_formula n v (~ α))
    have ih : derivable (row_to_formula n v α) := ih h1
    -- espandiamo le definizioni
    rw [row_to_formula, eval]
    cases ch : eval v α
    all_goals rw [row_to_formula, ch] at ih
    -- ora si danno due casi, o la formula α vale true o false
    -- Nota: qui non stiamo usando il terzo escluso. Perche'?
    case true => sorry
    case false => sorry
  -- Se φ = α → β
  | implies α β ih1 ih2 =>
    show derivable (row_to_formula n v (α → β))
    have ih1 : derivable (row_to_formula n v α) := ih1 h1.1
    have ih2 : derivable (row_to_formula n v β) := ih2 h1.2
    -- espandiamo le definizioni
    rw [row_to_formula, eval]
    cases ch1 : eval v α
    all_goals rw [row_to_formula, ch1] at ih1
    case false => sorry
    case true =>
      cases ch2 : eval v β
      all_goals sorry

/-
Ora inizia la seconda parte della dimostrazione, in cui dobbiamo riunire
tutte le dimostrazioni delle singole righe della tabella di verita' di φ
(che esistono grazie al main_lemma), in un'unica dimostrazione di φ.
Faremo uso del fatto seguente
  der_parametric_bycases  (derivable (α →  β → γ))
                          (derivable (α → ~β → γ)):
                                derivable (α → γ)
che e' dimostrato nella solita sezione nojosa. In che modo? Facciamo conto
di dover dimostrare φ che ha le variabili |0| ... |7|. Ogni riga della
tabella di verita' di φ ci ha dato una formula
  ~φ → ±|7| → ±|6| → ±|5| → ... → F
con il fatto precedente, prendendo α = ~φ, β = |7|, γ = ±|6| → ... → |F|,
partendo dalla deducibilita' di  
  ~φ →  |7| → ±|6| → ±|5| → ... → F
  ~φ → ~|7| → ±|6| → ±|5| → ... → F
otteniamo la deducibilita' di
  ~φ → ±|6| → ±|5| → ... → F
Procedendo cosi' possiamo consumare tutte le variabili, e ci troviamo ad
aver dimostrato (~φ → F), da cui concludiamo immediatamente grazie a
  der_remove_false (derivable (~ α → F)) : derivable α

Questa dimostrazione e' un po' piu' farraginosa di quanto ci si
aspetterebbe. Il guaio sta nel fatto che l'enunciato da dimostrare per
induzione e'
  P(n) = SE per ogni (v : Nat → Bool) la riga corrispondente,
                  ~φ → ±|n| → ±|n-1| → ... → F
            in cui i ± dipendono da v, e' deducibile
         ALLORA φ e' deducibile
Per fare il passo induttivo, pero', dobbiamo separare i casi (v n = true)
e (v n = false), ma questi casi non si risolvono tout court per ipotesi
induttiva, come a prima vista potrebbe sembrare. Perche' l'ipotesi
induttiva richiede che per ogni v valga una certa cosa, mentre in ciascun
caso noi lo sappiamo solo per i v con v n = true (o, rispettivamente,
false). La si puo' arrangiare in vari modi. O si lavora con un'ipotesi
induttiva piu' complicata. O si procede per induzione al contrario dal
caso n al caso 0, etc. Io ho scelto di dimostrare un lemma separato
suffix_depends_n che dice che il suffisso
  ±|n| → ±|n-1| → ... → |F|
dipende solo dai valori che (v m) assume su m ≤ n. Questo e' una
facilissima induzione su n.
-/

-- #check Nat.lt_succ_of_le
-- #check Nat.le_of_lt
-- #check Nat.lt_succ_self

theorem suffix_depends_n  {n : Nat} {v w : Nat → Bool}
                          (h : ∀ m , m < n → v m = w m) :
                          make_suffix n v = make_suffix n w := by
  induction n with
  | zero => sorry
  | succ p ih =>
    have : ∀ m , m < p → v m = w m := by
      sorry
    sorry

-- #check der_remove_false
-- #check der_parametric_bycases
-- #check Nat.ne_of_lt

theorem remove_suffix {φ : Formula} (n : Nat)
                      (h : ∀ v , derivable (~ φ → make_suffix n v)) : derivable φ := by
  induction n with
  | zero =>
      show derivable φ
      have h : ∀ v , derivable (~ φ → make_suffix 0 v) := h
      have : derivable (~ φ → F) := sorry
      sorry
  | succ m ih =>
    -- sfruttando l'ipotesi induttiva e fissando un v
    apply ih
    intro v
    -- dobbiamo dimostrare che
    show derivable (~ φ → make_suffix m v)
    -- e sappiamo
    have h : ∀ v , derivable (~ φ → make_suffix (m + 1) v) := h
    -- cominciamo col costruirci le due assegnazioni vf e vt danno a |m|
    -- i valori false e true rispettivamente
    let vf := fun x => if x = m then false else v x
    let vt := fun x => if x = m then true else v x
    have hvf : ∀ x , x < m → vf x = v x := by
      sorry
    have hvt : ∀ x , x < m → vt x = v x := by
      sorry
    -- ora applichiamo l'ipotesi induttiva a vf e ft rispettivamente
    skip
    -- e concludiamo con suffix_depends e der_parametric_bycases
    sorry

/-
Finalmente il risultato cercato
  completeness (valid φ) : derivable φ
Qui si tratta solo di tirare le somme. Usiamo exists_variables_lt per
procurarci l'ipotesi del main_lemma, il main_lemma per procurarci
l'ipotesi di remove_suffix, e remove_suffix per concludere.
-/

theorem completeness {φ : Formula} (h : valid φ) : derivable φ := by
  sorry

/-
Infine possiamo combinare le due frecce in un unico comodo enunciato.
-/

theorem valid_iff_derivable {φ : Formula} : valid φ ↔ derivable φ :=
  ⟨ completeness , soundness ⟩

/-
Postilla!

Chiaramente, il teorema valid_iff_derivable ci consente di dimostrare che
una formula e' deducibile senza bisogno di esibirne una deduzione:
facciamo un esempio.
-/

theorem ex_derivable : derivable (~ ~ |0| → |0|) := by
  have : valid (~ ~ |0| → |0|) := by
    rw [valid]
    intro v
    repeat rw [eval]
    cases v 0
    all_goals rfl
  exact valid_iff_derivable.1 this

/-
Ora, pero', la nostra dimostrazione e' formalizzata nel frammento
intuizionistico di Lean4, e, abbiamo detto, per Curry-Howard stabilisce un
isomorfismo fra le dimostrazioni e i lambda termini, cioe' gli algoritmi.
Cosa succedera' se chiediamo a Lean4 di ridurre ex_derivable?

Dopo aver completato tutti gli esercizi (non devono esserci piu' sorry,
altrimenti non funziona), togli il segno di commento dalla riga qua sotto,
poi armati di pazienza e aspetta...
-/

-- #reduce ex_derivable