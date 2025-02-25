import data.int.basic
import data.nat.prime

/-
Correctness 90/90
Style: 10/10
Good work Aqil
-/


/- This assignment is due by 11:59pm on Friday, March 10th 2023. -/

/-
EXERCISE 1. Using the definition `mypow a n`, which is supposed to define
exponentiation `a^n`, use induction to prove the theorem below.

Hint: you can use `nat.add_succ` to unfold the defition of `m + n.succ`.
-/

section
variables {α : Type*} [comm_monoid α]

def mypow : α → ℕ → α
| a 0       := 1
| a (n + 1) := a * (mypow a n)

#eval mypow 3 5

theorem mypow_zero (a : α) : mypow a 0 = 1 := rfl

theorem mypow_succ (a : α) (n : ℕ) : mypow a (n + 1) = a * mypow a n := rfl

-- Exercise 1 [10pts].
theorem mypow_add (a : α) (m n : ℕ) : mypow a (m + n) = mypow a m * mypow a n :=
begin
  induction n with n ih,
  {
    rw mypow_zero,
    simp,
  },
  rw nat.add_succ,
  rw mypow_succ,
  rw mypow_succ,
  rw ih,
  exact mul_left_comm a (mypow a m) (mypow a n),
end

end

/-
EXERCISE 2.

In class, we have used ordinary induction on the natural numbers,
which allows you to prove `p n` for an arbitrary natural number
`n` by proving `p 0` and `∀ m, p m → p m.succ`.

It is often more useful to the principle of *complete induction*
or *strong induction*. This is found in the library under the
name `nat.strong_induction_on`, but the exercise below asks you
to prove it independently, using ordinary induction on the natural numbers.
The principle is stated in a form that the induction tactic
can use it, as illustrated in exercise 3.

The trick is to prove the stronger claim `∀ n, ∀ m < n, p m` by
induction on the natural numbers. The `suffices` step in the proof
shows that this suffices to establish `p n` for the *particular* `n` in
the context. Once we have done that, we throw away the particular `n`,
and focus on proving the stronger claim by induction.
-/

section

-- Exercise 2 [17pts].
theorem complete_induction_on {p : ℕ → Prop} (n : ℕ)
  (h : ∀ n, (∀ m < n, p m) → p n) : p n :=
begin
  suffices : ∀ n, ∀ m < n, p m,
  {exact h n (this n),},
  clear n,
  intro n,
  induction n with n ih,
  {simp,},
  intros m h1,
  have mlen : m ≤ n, 
  {apply nat.lt_succ_iff.1 h1,},
  have h2 : m < n ∨ m = n,
  {apply le_iff_lt_or_eq.1 mlen,},
  cases h2,
  {
    specialize ih m,
    apply ih h2,
  },
  rw h2,
  specialize h n,
  apply h ih,
end

end

/-
EXERCISE 3.

In this exercise, we use the principle of strong induction to show that
every natural number greater than or equal to two has a prime divisor.

You can use the lemma `exists_lt_dvd_of_not_prime`. After the boilerplate
that we have set up for you, you should formalize the following argument:
if `n` is prime, we are done.  If `n` is not prime, the lemma tells us that
there it has a nontrivial divisor `m < n`, and we can apply the induction
hypothesis to that.
-/

-- This follows straightforwardly from the definition of `nat.prime`.
lemma exists_lt_dvd_of_not_prime {n : nat} (h : ¬ nat.prime n) (h' : 2 ≤ n) :
  ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n :=
begin
  simp [nat.prime_def_lt'] at h,
  exact h h'
end


-- Exercise 3 [18pts].
theorem exists_prime_dvd (n : ℕ) : 2 ≤ n → ∃ p, nat.prime p ∧ p ∣ n :=
begin
  induction n using complete_induction_on with n ih,
  dsimp at ih,
  intro nle,
  by_cases nprime : nat.prime n,
  {
    use n,
    simp,
    exact nprime,
  },
  have divisor : ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n,
  {apply exists_lt_dvd_of_not_prime nprime nle,},
  cases divisor with m divisorm,
  specialize ih m,
  rcases divisorm with ⟨m1, m2, m3⟩,
  have h : 2 ≤ m → (∃ (p : ℕ), nat.prime p ∧ p ∣ m),
  {apply ih m2,},
  have h1 : (∃ (p : ℕ), nat.prime p ∧ p ∣ m),
  {apply h m1,},
  cases h1 with p hp,
  use p,
  split,
  exact hp.1,
  apply dvd_trans hp.2 m3,
end

/-
EXERCISE 4.

Finally, in this exercise, we define the structure of a `quasigroup`,
show that the integers with subtraction form an instance, and prove
some basic properties.

You can find the definition of a quasigroup here:

  https://en.wikipedia.org/wiki/Quasigroup

We'll use the notation `ldiv a b` for left division (on Wikipedia, `a \ b`),
and we'll use `rdiv a b` for right division (on Wikipedia, `a / b`).

(Instantiating the integers as a quasigroup is dangerous, because it
redefines the notation of multiplication to mean substraction. Such 
a thing could destroy the understanding of mathematics for a generation 
of elementary school students, so please make sure your git repositories 
stay private!)
-/

-- Exercise 4a [10pts].
/-
First, fill in the remaining axioms. E.g. the first should say,
"for any `a`, `b` and `x`, if `x` satisfies the defining equation for `a \ b`
(that is, the cancellation law), then it is equal to `a \ b`."
-/

class quasigroup (α : Type*) extends has_mul α :=
(ldiv : α → α → α)
(rdiv : α → α → α)
(mul_ldiv_cancel : ∀ a b, a * ldiv a b = b)
(rdiv_mul_cancel : ∀ a b, rdiv a b * b = a)
(ldiv_unique : ∀ a b x, (a * x = b) → (x = ldiv a b))
(rdiv_unique : ∀ a b x, (x * b = a) → (x = rdiv a b))

-- Exercise 4b [15pts].
/-
Next, show that the integers with subtraction are an instance. You will
have to figure out the right definitions of `ldiv` and `rdiv`. For
example, if you decide `ldiv a b` should be `a * b`, write
`ldiv := λ a b, a * b`.

Note: Be sure to write this out on paper first, and check the identities
as you see them wikipedia.  This will make the coding much easier, and 
help avoid you trying to prove something that is impossible. 

Note that in goals within the instance definition, you might see "multiplication"
which is really integer subtraction, because that's we defined it as! To check
which one it really is, you can click on the `*` operation in the infoview and look
for something like `{mul := int.sub}`.

Also, the `show` tactic can sometimes be used to unfold definitions. For example
on the goal `⊢ a * b = stuff`, `show a - b = stuff` should work.
-/

instance : quasigroup ℤ :=
{ mul := int.sub,
  ldiv := λ a b, a - b,
  rdiv := λ a b, b - (-a),
  mul_ldiv_cancel :=
    begin
      intros a b,
      show a - (a - b) = b,
      simp,
    end,
  rdiv_mul_cancel :=
    begin
      intros a b,
      show (b - -a) - b = a,
      simp,
  end,
  ldiv_unique :=
    begin
      intros a b x,
      show a - x = b → x = a - b,
      intro h,
      rw ←h,
      simp,  
    end,
  rdiv_unique :=
    begin
      intros a b x,
      show x - b = a → x = b - -a,
      intro h,
      simp,
      rw ←h,
      simp, 
    end }

/- Finally, prove that some identities hold in *any* quasigroup. -/

namespace quasigroup
variables {α : Type*} [quasigroup α]

-- Exercise 4c [5pts].
theorem eq_ldiv_mul_self (y x : α) : y = ldiv x (x * y) :=
begin
  apply ldiv_unique,
  simp,
end

-- Exercise 4d [5pts].
theorem eq_mul_rdiv_self (y x : α) : y = rdiv (y * x) x :=
begin
  apply rdiv_unique,
  simp,
end

-- Exercise 4e [10pts].
theorem left_cancel (a b c : α) (h : a * b = a * c) : b = c :=
begin
  have lhs : b = ldiv a (a * b),
  {apply eq_ldiv_mul_self b a,},
  rw lhs,
  have rhs : c = ldiv a (a * c),
  {apply eq_ldiv_mul_self c a,},
  rw rhs,
  rw h,
end

-- Exercise 4f [10pts].
theorem right_cancel (a b c : α) (h : a * b = c * b) : a = c :=
begin
  have lhs : a = rdiv (a * b) b,
  {apply eq_mul_rdiv_self a b,},
  rw lhs,
  have rhs : c = rdiv (c * b) b,
  {apply eq_mul_rdiv_self c b,},
  rw rhs,
  rw h,
end

end quasigroup

