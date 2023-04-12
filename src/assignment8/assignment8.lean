import data.real.basic
import data.matrix.basic

/-
Correctness 90/90
Style: 10/10
Good work Aqil
-/



/-
EXERCISE 1.

In set theory, one typically builds up a foundation for reasoning about finite
sets as follows. First, one defines the set of natural numbers. Then one says
that a set is *finite* if it is in bijection with the set {0, 1, ..., n-1} for
some n. We then want to say that the *cardinality* of that set is n, but that
requires knowing that a set cannot be in bijection with the canonical n-element
set and the canonical m-element set at the same time if m ≠ n. This can be
reduced to showing that there is no injective function from the canonical
n-element set to the canonical n-1-element set. This is the pigeonhole
principle, below.

This is *not* how it is done in mathlib. For the record, there we do the
following:

- Define the type of lists.
- Say what it means for one list to be a permutation of another, and prove that
  this is an equivalence relation.
- Define multisets to be lists modulo permutation equivalence.
- Define finsets to be multisets without duplicates.

Operations like union, intersection, cardinality are defined on lists and
lifted to multisets.

The next proof of the pigeonhole principle is pretty messy. I'd love to see a
cleaner one (that doesn't use finsets!).
-/

section
variable {α : Type*}
--open finset

-- Exercise 1 [40pts]. Fill in the sorries below.
theorem pigeonhole_principle (n : ℕ) :
  ∀ f : ℕ → ℕ, (∀ i ≤ n, f i < n) → ∃ i ≤ n, ∃ j ≤ n, i ≠ j ∧ f i = f j :=
begin
  induction n with n ih,
  {simp,},
  intros f hf,
  -- In the inductive step, if f is an injection from {0...n} to {0...n-1}, we
  -- are done.
  by_cases h : ∀ i ≤ n, f i < n,
  { specialize ih f,
    have h1 : ∃ (i : ℕ) (H : i ≤ n) (j : ℕ) (H : j ≤ n), i ≠ j ∧ f i = f j,
    {apply ih h,},
    cases h1 with i hi,
    use i,
    cases hi with ileqn hi,
    cases hi with j hj,
    cases hj with jleqn ij,
    split,
    apply nat.le_succ_of_le ileqn,
    use j,
    split,
    apply nat.le_succ_of_le jleqn,
    exact ij,
  },
  -- Otherwise, f maps some element less or equal to n to n.
  push_neg at h,
  rcases h with ⟨i, hi, nle⟩,
  have := hf i (nat.le_succ_of_le hi),
  have fieq : f i = n := le_antisymm (nat.le_of_lt_succ this) nle,
  -- If it maps some other element less than or equal to n + 1 to n, then f is
  -- not injective on {0...n+1}, and we are done.
  by_cases h' : ∃ j ≤ n.succ, i ≠ j ∧ f j = n,
  { rcases h' with ⟨j, jle, inej, fjeq⟩,
    use [i, nat.le_succ_of_le hi, j, jle, inej, fieq.trans fjeq.symm] },
  -- Otherwise, there is only one element less than n which gets sent to n, namely i.
  -- We define f' to instead map i to the value of f n.succ, and apply the inductive
  -- hypothesis to f'.
  -- Note the use of the `split_ifs` tactic.
  push_neg at h',
  set f' := λ j, if j = i then f n.succ else f j with f'def,
  have : ∀ j ≤ n, f' j < n,
  { intros j jle,
    dsimp [f'], split_ifs with h0 h1,
    { have : f n.succ ≠ n,
      {
        by_contra,
        specialize h' n.succ,
        simp at h',
        have iltnsucc : i < n.succ,
        { rw nat.lt_succ_iff,
          exact hi,
        },
        have ineqnsucc : i ≠ n.succ,
        {apply ne_of_lt iltnsucc,},
        have contra : f n.succ ≠ n,
        {apply h' ineqnsucc,}, 
        contradiction,
      },
      exact lt_of_le_of_ne (nat.le_of_lt_succ (hf _ (le_refl _)))
        this, },
    apply lt_of_le_of_ne _ (h' j (nat.le_succ_of_le jle) (ne.symm h0)),
    apply nat.le_of_lt_succ (hf j (nat.le_succ_of_le jle)) },
  rcases ih f' this with ⟨j, jle, k, kle, jnek, f'eq⟩,
  rw f'def at f'eq, dsimp at f'eq,
  -- This produces four goals, one for each combination of true/false in the two `ite`s.
  split_ifs at f'eq with h0 h1 h2 h3,
  { subst h0, subst h1, contradiction },
  { use [n.succ, le_rfl, k, nat.le_succ_of_le kle, 
         (ne_of_lt (nat.lt_succ_of_le kle)).symm, f'eq], },
  -- The two cases below are quite analogous to the one directly above.
  { use n.succ,
    split,
    simp,
    use j,
    split,
    have jleqnsucc : j ≤ n.succ,
    {
      transitivity n,
      exact jle,
      apply nat.le_succ,
    },
    exact jleqnsucc,
    split,
    have jneqnsucc : n.succ ≠ j,
    {
      by_contra,
      rw ← h at jle,
      have nltnsucc : n < n.succ,
      {apply nat.lt_succ_self n,},
      have contra : ¬ n.succ ≤ n,
      {apply not_le_of_lt nltnsucc,},
      contradiction,
    },
    exact jneqnsucc,
    symmetry,
    exact f'eq,
  },
  use k,
  have kleqnsucc : k ≤ n.succ,
    {
      transitivity n,
      exact kle,
      apply nat.le_succ,
    },
  split,
  exact kleqnsucc,
  use j,
  have jleqnsucc : j ≤ n.succ,
  {
    transitivity n,
    exact jle,
    apply nat.le_succ,
  },
  split,
  exact jleqnsucc,
  split,
  symmetry,
  exact jnek,
  symmetry,
  exact f'eq,
end
end

/-
EXERCISE 2. The following is an exercise on structural induction on formulas.
-/

inductive PropForm : Type
| var (n : ℕ)           : PropForm
| fls                   : PropForm
| conj (A B : PropForm) : PropForm
| disj (A B : PropForm) : PropForm
| impl (A B : PropForm) : PropForm

namespace PropForm

def eval : PropForm → (ℕ → bool) → bool
| (var n)    v := v n
| fls        v := ff
| (conj A B) v := A.eval v && B.eval v
| (disj A B) v := A.eval v || B.eval v
| (impl A B) v := !! A.eval v || B.eval v

def subst : PropForm → ℕ → PropForm → PropForm
| (var n)    m C := if n = m then C else var n
| fls        m C := fls
| (conj A B) m C := conj (A.subst m C) (B.subst m C)
| (disj A B) m C := disj (A.subst m C) (B.subst m C)
| (impl A B) m C := impl (A.subst m C) (B.subst m C)

def free_variables : PropForm → finset ℕ
| (var n)    := {n}
| fls        := ∅
| (conj A B) := A.free_variables ∪ B.free_variables
| (disj A B) := A.free_variables ∪ B.free_variables
| (impl A B) := A.free_variables ∪ B.free_variables

theorem subst_eq_of_not_mem_free_variables :
  ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.free_variables →
      A.subst n C = A
| (var m) n C h :=
    begin
      rw [subst], split_ifs with h0 h0,
      { simp [h0, free_variables] at h,
        contradiction },
      refl
    end
| fls n C h := by rw [subst]
| (conj A B) n C h :=
    begin
      rw [subst, subst_eq_of_not_mem_free_variables A,
            subst_eq_of_not_mem_free_variables B];
        simp [free_variables] at h; tauto
    end
| (disj A B) n C h :=
    begin
      rw [subst, subst_eq_of_not_mem_free_variables A,
            subst_eq_of_not_mem_free_variables B];
        simp [free_variables] at h; tauto
    end
| (impl A B) n C h :=
    begin
      rw [subst, subst_eq_of_not_mem_free_variables A,
            subst_eq_of_not_mem_free_variables B];
        simp [free_variables] at h; tauto
    end

-- Exercise 2 [30pts].
theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → bool),
  (A.subst n C).eval v = A.eval (λ m, if m = n then C.eval v else v m)
| (var m) n C v :=
    begin
      rw subst,
      rw eval,
      split_ifs,
      refl,
      rw eval,
    end
| fls n C v :=
    begin
      rw subst,
      rw eval,
      rw eval,
    end
| (conj A B) n C v :=
    begin
      rw subst,
      rw eval,
      rw eval,
      simp [subst_eval_eq],
    end
| (disj A B) n C v :=
    begin
      rw subst,
      rw eval,
      rw eval,
      simp [subst_eval_eq],
    end
| (impl A B) n C v :=
    begin
      rw subst,
      rw eval,
      rw eval,
      simp [subst_eval_eq],
    end

end PropForm

/-
EXERCISE 3. This is an exercise in defining the integers as a quotient
with (p.1, p.2) representing the equivalence class of p.1 - p.2.
(It's not the definition used in mathlib, but at one time it was.)
-/

def iequiv (p q : ℕ × ℕ) := p.1 + q.2 = q.1 + p.2

theorem equivalence_iequiv : equivalence iequiv :=
⟨λ p, rfl, λ p q h, h.symm, λ p q r h1 h2,
  begin
    simp [iequiv] at *,
    linarith,
  end⟩

def isetoid : setoid (ℕ × ℕ) := ⟨iequiv, equivalence_iequiv⟩

def integer := quotient isetoid

local attribute [instance] isetoid

def izero : integer := ⟦(0, 0)⟧

def iadd : integer → integer → integer :=
quotient.lift₂
  (λ p q : ℕ × ℕ, ⟦(p.1 + q.1, p.2 + q.2)⟧)
  begin
    intros a₁ a₂ b₁ b₂,
    dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv],
    intros h1 h2,
    apply quotient.sound,
    dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv],
    linarith
  end

def iadd_comm (a b : integer) : iadd a b = iadd b a :=
begin
  apply quotient.induction_on₂ a b,
  intros p q,
  simp [iadd],
  dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv],
  abel
end

def iadd_zero (a : integer) : iadd a izero = a :=
begin
  apply quotient.induction_on a,
  intro p,
  simp [iadd, izero],
end

-- Define negation and prove that it works.

-- Exercise 3a [15pts].
def ineg : integer → integer := quotient.lift (λ p : ℕ × ℕ, ⟦(p.2, p.1)⟧)
begin
  intros a b h,
  dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv],
  simp,
  dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv],
  dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv] at h,
  linarith,
end


-- Exercise 3b [15pts].
theorem iadd_ineg (a : integer) : iadd a (ineg a) = izero :=
begin
  apply quotient.induction_on a,
  intro b,
  simp [iadd, izero, ineg],
  dsimp [has_equiv.equiv, isetoid, setoid.r, iequiv],
  linarith,
end

