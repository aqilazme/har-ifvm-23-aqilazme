import tactic
import data.set

/-
# Theorems of Propositional Logic
-/

--1) Soundness Theorem for Propositional Logic
--Theorem: Let Γ be a set of sentences/formulas in propositional logic, where Γ = A₁, A₂, ..., A_n
--If Γ syntactically entails C, then Γ semantically implies C 
--In other words, if Γ ⊢ C, then Γ ⊨ C
--Reference: https://en.wikipedia.org/wiki/Soundness


--First we define atomic propositions as the basic building blocks of this language
--Since Lean already has "Prop" as a type that truth-values can be assigned to, we can utilize that
--Lean also already has all the logical connectives necessary
variables p q r : Prop
--Lean is also able to recognize the composition of atomic propositions and connectives as type "Prop" 
--This means the entire thing is recognized as a formula/sentence
#check p → (q ∧ ¬r)

--Then, we define the rules of inference in propositional logic
--Reference: https://en.wikipedia.org/wiki/Rule_of_inference
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
--Note: One further exercise I could do is to show how these rules are derived from the three or four 
--axioms of propositional logic. However, I don't think it is necessary or important at this point because
--these rules seem widely accepted as they are


--Then, we define the notion of a proof that uses these rules of inference
--More References for my personal use as I'm working on this project: https://risingentropy.com/proving-the-completeness-of-propositional-logic/

inductive provable (Γ : set Prop) : Prop → Type
| assumption (p : Prop) : p ∈ Γ → provable p
| implication_introduction (p q : Prop) : (p → q ∈ Γ) → provable p → provable q
| modus_ponens (p q : Prop) : provable (p → q) → provable p → provable q



--Then, we define the concept of syntactic entailment (derivation)

--Then, we define the concept of semantic implication (tautological entailment)

--Then, we need to prove Deduction Theorem
--Theorem: If a formula B is deducible from the set of assumptions Γ ∪ {A}
--Then, the implication A → B is deducible from Γ
--In other words, Γ ∪ {A} ⊢ B implies Γ ⊢ A → B 
--Reference: https://en.wikipedia.org/wiki/Deduction_theorem

theorem deduction_theorem (Γ : set Prop) (A B : Prop) : ((Γ ∪ {A}) ⊢ B) → (Γ ⊢ (A → B)) :=

--Then, we prove soundness theorem by induction



--2) Completeness Theorem for Propositional Logic

