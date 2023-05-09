import tactic
import data.set
import data.list.basic

open_locale classical

/-
# Theorems of Propositional Logic
-/

--First we define atomic propositions as the basic building blocks of this language
--Since Lean already has "Prop" as a type that truth-values can be assigned to, we can utilize that
--Lean also already has all the logical connectives necessary
variables p q r : Prop
--Lean is also able to recognize the composition of atomic propositions and connectives as type "Prop" 
--This means the entire thing is recognized as a formula/sentence
#check p → (q ∧ ¬r)

--Then, we need to define the notion of derivation in logic and the rules of inferences that are allowed
--Reference: https://en.wikipedia.org/wiki/Rule_of_inference
/-
inductive derivation (Γ : set Prop) : Prop → Prop
| assumption (p : Prop) : p ∈ Γ → derivation p
| modus_ponens (p q : Prop) : derivation (p → q) → derivation p → derivation q
| modus_tollens (p q : Prop) : derivation (p → q) → derivation ¬q → derivation ¬p
| disjunctive_syllogism_left (p q : Prop) : derivation (p ∨ q) → derivation ¬p → derivation q
| disjunctive_syllogism_right (p q : Prop) : derivation (p ∨ q) → derivation ¬q → derivation p
| simplification_left (p q : Prop) : derivation (p ∧ q) → derivation p
| simplification_right (p q : Prop) : derivation (p ∧ q) → derivation q
| conjunction (p q : Prop) : derivation p → derivation q → derivation (p ∧ q)
| hypothetical_syllogism (p q r: Prop) : derivation (p → q) → derivation (q → r) → derivation (p → r)
| addition_left (p q : Prop) : derivation p → derivation (p ∨ q)
| addition_right (p q : Prop) : derivation q → derivation (p ∨ q)
| constructive_dilemma (p q r s: Prop) : derivation (p → q) → derivation (r → s) → derivation (p ∨ r) → derivation (q ∨ s)
-/

--Axioms of Propositional Logic:
axiom axiom1 (φ : Prop) (ψ : Prop) : φ → (ψ → φ)
axiom axiom2 (φ : Prop) (ψ : Prop) (ζ : Prop) : (φ → (ψ → ζ)) → ((φ → ψ) → (φ → ζ))
axiom axiom3 (φ : Prop) (ψ : Prop) : (¬φ → ¬ψ) → (ψ → φ)

inductive derivation (Γ : set Prop) : Prop → Prop
| assumption (p : Prop) : p ∈ Γ → derivation p
| modus_ponens (p q : Prop) : derivation (p → q) → derivation p → derivation q

axiom axiom1_derivation (Γ : set Prop) (p q : Prop) : derivation Γ p → derivation Γ (p → (q → p))
axiom axiom2_derivation (Γ : set Prop) (p q r : Prop) : derivation Γ (p → (q → r)) → derivation Γ ((p → q) → (p → r))
axiom axiom3_derivation (Γ : set Prop) (p q : Prop) : derivation Γ (¬p → ¬q) → derivation Γ (q → p)    

--Then, we shall prove that each of these rules work in Lean:

theorem modus_ponens (p q : Prop) : (p → q) → p → q :=
begin
  intro h,
  exact h,
end

theorem modus_tollens (p q : Prop) : (p → q) → ¬q → ¬p :=
begin
  intro h,
  intro nq,
  intro hp,
  apply nq,
  apply h hp,
end

theorem disjunctive_syllogism_left (p q : Prop) : (p ∨ q) → ¬p → q :=
begin
  intro h,
  cases h,
  intro np,
  contradiction,
  intro np,
  exact h,
end

theorem disjunctive_syllogism_right (p q : Prop) : (p ∨ q) → ¬q → p :=
begin
  intro h,
  cases h,
  intro np,
  exact h,
  contradiction,
end

theorem simplification_left (p q : Prop) : (p ∧ q) → p :=
begin
  intro h,
  exact h.1,
end

theorem simplification_right (p q : Prop) : (p ∧ q) → q :=
begin
  intro h,
  exact h.2,
end

theorem conjunction (p q : Prop) : p → q → (p ∧ q) :=
begin
  intro p,
  intro q,
  split,
  exact p,
  exact q,
end

theorem hypothetical_syllogism (p q r: Prop) : (p → q) → (q → r) → (p → r)  :=
begin
  intro h1,
  intro h2,
  intro p,
  have q : q,
  {apply h1 p,},
  have r : r,
  {apply h2 q,},
  exact r,
end

theorem addition_left (p q : Prop) : p → (p ∨ q) :=
begin
  intro h,
  left,
  exact h,
end

theorem addition_right (p q : Prop) : q → (p ∨ q) :=
begin
  intro h,
  right,
  exact h,
end

theorem constructive_dilemma (p q r s: Prop) : (p → q) → (r → s) → (p ∨ r) → (q ∨ s)  :=
begin
  intro h1,
  intro h2,
  intro h3,
  cases h3,
  left,
  apply h1 h3,
  right,
  apply h2 h3,
end

--Then, we define the concept of syntactic entailment (derivation) i.e. the symbol ⊢

def entails (Γ : set Prop) (c : Prop) : Prop :=  derivation Γ c

axiom entails_true (Γ : set Prop) : entails Γ true 

--Then, we define the concept of semantic implication (tautological entailment) i.e. the symbol ⊨
--In propositional logic, we say that A ⊨ B if all valuations that satisfy A also satisfy B
--We say that valuation (denoted v) is an assignment of truth values to sentences that obeys the functional relationships given by the truth tables

def semantic_implication (p : Prop) (q : Prop) : Prop := ∀ (v : Prop → bool), (v p = true) → (v q = true)
def semantic_implication_set (Γ : set Prop) (C : Prop) : Prop := ∀ (v : Prop → bool), (∀ p ∈ Γ, v p = true) → (v C = true)

--We would need to define the modus ponens rule over this type as well:
def v_modus_ponens (v : Prop → bool) (h1 : v (p → q) = tt) (h2 : v p = tt) : (v q = tt) := sorry


--1) Deduction Theorem for Propositional Logic
--Theorem: If a formula B is deducible from the set of assumptions Γ ∪ {A}
--Then, the implication A → B is deducible from Γ
--In other words, Γ ∪ {A} ⊢ B implies Γ ⊢ A → B

/-
# It's supposed to be iff for Deduction Theorem
-/

theorem deduction (Γ : set Prop) (A B : Prop) : (entails (Γ ∪ {A}) B) → (entails Γ (A → B)) :=
begin
  intro h,
  induction h with d hd p q h1 h2 h3 h4,
  cases hd,
  {
    have h1 : entails Γ d,
    {
      apply derivation.assumption,
      exact hd,
    }, 
    have h2:  derivation Γ (d → (A → d)),
    {
      apply axiom1_derivation,
      exact h1,
    },
    apply derivation.modus_ponens d,
    exact h2,
    exact h1,
  },
  {
    rw set.mem_singleton_iff at hd,
    rw hd,
    simp,
    apply entails_true,
  },
  have h : derivation Γ ((A → p) → (A → q)),
  {
    apply axiom2_derivation,
    exact h3,
  },
  unfold entails at h4,
  have h5 : derivation Γ (A → q),
  {
    apply derivation.modus_ponens (A → p),
    exact h,
    exact h4,
  },
  apply h5,
end

--2) Soundness Theorem for Propositional Logic
--Theorem: Let Γ be a set of sentences/formulas in propositional logic, where Γ = A₁, A₂, ..., A_n
--If Γ syntactically entails C, then Γ semantically implies C 
--In other words, if Γ ⊢ C, then Γ ⊨ C

theorem soundness (Γ : set Prop) (C : Prop) : (entails Γ C) → (semantic_implication_set Γ C) :=
begin
  intro h,
  unfold semantic_implication_set,
  intros v hv,
  induction h with d hd p q h1 h2 h3 h4,
  {
  specialize hv d,
  apply hv hd,
  },
  specialize hv q,
  have h5 : derivation Γ q,
  {
    apply derivation.modus_ponens p,
    exact h1,
    exact h2,
  }, 
  cases h5 with h5 h5 r h6 h7,
  {
    apply hv h5,
  },
  have h8 : derivation Γ q,
  {
    apply derivation.modus_ponens r,
    exact h7,
    exact h5_ᾰ,
  }, 
  simp at h3,
  simp at h4,
  simp,
  apply v_modus_ponens p,
  exact h3,
  exact h4,
end

--3) Completeness Theorem for Propositional Logic
--Theorem: Let Γ be a set of sentences/formulas in propositional logic, where Γ = A₁, A₂, ..., A_n
--If Γ semantically implies C, then Γ syntatically entails C 
--(If C is a tautology (logically valid) then there exists a proof of C using only the inference rules of propositional logic)
--In other words, if Γ ⊨ C, then Γ ⊢ C

--Since propositional logic is functionally complete using only two logical connectives, which is
--negation and implication, we will only consider these two, as in our proof on paper

inductive atom : Type
| sentence : ℕ → atom 

inductive formula : Type
| atom : atom → formula
| not : formula → formula
| implies : formula → formula → formula

def atomic_sentences : formula → list atom
| (formula.atom a) := [a]
| (formula.not A) := atomic_sentences A
| (formula.implies A B) := atomic_sentences A ++ atomic_sentences B

def valuation := atom → bool

def v_star (v : valuation) : formula → bool
| (formula.atom a) := v a
| (formula.not A) := ¬ (v_star A)
| (formula.implies A B) := (v_star A) → (v_star B)

def A_prime (v : valuation) (A : formula) : formula :=
if v_star v A then A else formula.not A

def corresponding_formulae (v : valuation) (A : formula) : list formula :=
let b_list := atomic_sentences A in
A_prime v A :: (b_list.map (λ b, if v b then formula.atom b else formula.not (formula.atom b)))

structure sequent :=
(Γ : list formula)
(Δ : formula)

constant entail : sequent → Prop

def degree : formula → ℕ
| (formula.atom _) := 0
| (formula.not A) := degree A + 1
| (formula.implies A B) := degree A + degree B + 1

instance inhabited_atom : inhabited atom :=
  ⟨atom.sentence 0⟩

instance : inhabited formula := ⟨formula.atom default⟩

--We need to define a lemma that would help us rewrite the list of atomic sentences
--minus the first one when we are working on the main lemma
lemma tail_corresponding_formulae_atomic_sentences {v : valuation} {A : formula} :
  (corresponding_formulae v A).tail = list.map (λ (b : atom), ite ↥(v b) (formula.atom b) (formula.atom b).not) (atomic_sentences A) :=
begin
  induction A with a A₁ ih A₁ A₂ ih1 ih2,
  --Case: A = formula.atom a
  {
    simp [corresponding_formulae, atomic_sentences],
  },
  --Case: A = A₁.not
  {
    simp [corresponding_formulae],
  },
  --Case: A = A₁ → A₂
  {
    simp [corresponding_formulae],
  }
end

--We also need to define the tautology that the negation of a negation is the same formula
axiom negation_of_negation (A : formula) : A.not.not = A

lemma main_lemma (v : valuation) (A : formula) : 
  let f_list := corresponding_formulae v A in
  (∀ i, i ∈ f_list → (degree i < degree A)) → entail {Γ := list.tail f_list, Δ := A_prime v A} :=
begin
  intro h,
  induction A with a A₁ ih A₁ A₂ ih1 ih2,
  --Base case, n = 0 i.e. A = a
  {
    intro h1,
    change (entail {Γ := list.tail (corresponding_formulae v (formula.atom a)), Δ := A_prime v (formula.atom a)}),
    rw corresponding_formulae,
    rw A_prime,
    rw list.tail_cons,
    have h_basecase : atomic_sentences (formula.atom a) = [a],
    {
      simp [atomic_sentences],
    },
    rw h_basecase,
    simp,
    have v_star_a : v_star v (formula.atom a) = v a,
    {
      simp [v_star],
    },
    cases v a,
    swap,
    --Case 1 : v*(A)=true
    {
      rw v_star_a,
      simp,
      --tautology
      sorry,
    },
    --Case 2 : v*(A)=false
    {
      rw v_star_a,
      simp,
      --tautology
      sorry,
    },
  },
  --Inductive step
  --Case 1: A is ¬A₁
  {
    intro h1,
    change (entail {Γ := list.tail (corresponding_formulae v (A₁)), Δ := A_prime v (A₁.not)}),
    rw corresponding_formulae,
    rw A_prime,
    rw list.tail_cons,
    have hdegree : degree (A₁) < degree (A₁.not),
    {
      simp [degree],
    },
    have h2 : (∀ (i : formula), i ∈ corresponding_formulae v A₁ → degree i < degree A₁),
    {
      intros i hi,
      rw corresponding_formulae at hi,
      simp at hi,
      sorry
    },
    have ih_A₁ := ih h2,
    rw A_prime,
    --have v_star_a : v_star v (A₁.not) = v A₁,
    cases v_star v A₁.not,
    swap,
    --Case 1a) v*(A)=true
    {
      simp,
      rw ←tail_corresponding_formulae_atomic_sentences,
      simp,
      rw A_prime at ih_A₁,
      have h3 : v_star v A₁ = ff,
      {
        sorry,
      },
      rw h3 at ih_A₁,
      simp at ih_A₁,
      exact ih_A₁,
    },
    --Case 1b) v*(A)=false
    {
      simp,
      rw ←tail_corresponding_formulae_atomic_sentences,
      simp,
      rw A_prime at ih_A₁,
      have h3 : v_star v A₁ = tt,
      {
        sorry,
      },
      rw h3 at ih_A₁,
      simp at ih_A₁,
      rw negation_of_negation,
      exact ih_A₁,
    },
  },
  --Case 2: A is A₁ → A₂
  {
    intro h1,
    change (entail {Γ := list.tail (corresponding_formulae v (A₁.implies A₂)), Δ := A_prime v (A₁.implies A₂)}),
    rw corresponding_formulae,
    rw A_prime,
    rw list.tail_cons,
    have h2 : (∀ (i : formula), i ∈ corresponding_formulae v A₁ → degree i < degree A₁),
    {
    intros i hi,
    sorry,
    },
    have h3 : (∀ (i : formula), i ∈ corresponding_formulae v A₂ → degree i < degree A₂),
    {
    intros i hi,
    sorry,
    },
    have ih_A₁ := ih1 h2,
    have ih_A₂ := ih2 h3,
    cases v_star v A₁, 
    cases v_star v A₂,
    --Case 2a: v*(A₁)=v*(A₂)=true
    {
      rw ←tail_corresponding_formulae_atomic_sentences,
      simp,
      sorry,
    },
    --Case 2b: v*(A₁)=true, v*(A₂)=false
    {
      rw ←tail_corresponding_formulae_atomic_sentences,
      simp,
      sorry,
    },
    --Case 2c: v*(A₁)=false
    {
      rw ←tail_corresponding_formulae_atomic_sentences,
      simp,
      sorry,
    },
  }
end

--We then need to redefine semantic implication that works for type list formula and formula
def semantically_implies (Γ : list formula) (A : formula) : Prop :=
∀ (v : valuation), (∀ B ∈ Γ, v_star v B = tt) → v_star v A = tt

theorem completeness (Γ : list formula) (A : formula) : (semantically_implies Γ A) → (entail { Γ := Γ, Δ := A }) := 
begin
  intro h,
  sorry
end
