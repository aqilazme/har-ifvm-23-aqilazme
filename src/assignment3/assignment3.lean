import data.real.basic

/-
Correctness 90/90
Style: 10/10
Good work Aqil
-/


/-
FIRST EXERCISE: Strict monotonicity

Section 3.1 of MIL discusses the `monotone` predicate. There is also a strict
version. Prove the theorems below, *and* come up with suitable names
(in other words, replace `example` with `theorem foo`.)

(Don't use any library theorems about `strict_mono` or `monotone`! You should
only use basic properties of orderings.)
-/

#print monotone. 
#print strict_mono. 

namespace strict_mono_exercise

variables (f : ℝ → ℝ) (g : ℝ → ℝ)

theorem sum_of_strict_mono_is_strict_mono (hf : strict_mono f) (hg : strict_mono g) : strict_mono (f + g) :=
begin
  unfold strict_mono,
  intro a,
  intro b,
  intro alb,
    {
      dsimp,
      specialize hf alb,
      specialize hg alb,
      exact add_lt_add hf hg,
    },
end

-- You'll have to guess at the name of a theorem for this one.
theorem scaling_strict_mono (c : ℝ) (hf : strict_mono f) (hc : 0 < c) :
  strict_mono (λ x, c * f x) :=
begin
  unfold strict_mono,
  intro a,
  intro b,
  intro alb,
  have falfb : f a < f b,
    begin
      apply hf alb,
    end,
  exact (mul_lt_mul_left hc).mpr falfb,
end

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.

theorem strict_mono_implies_mono (hf : strict_mono f) : monotone f :=
begin
  unfold monotone,
  intro a,
  intro b,
  intro aleqb,
  by_cases h : a = b,
    { apply le_of_eq,
      exact congr_arg f h,
    },
  {
    have alb : a < b,
    {
      apply lt_of_le_of_ne aleqb h,
    },
    apply le_of_lt,
    exact hf alb,
  },
end

/-
The following (trivial) example shows how to use trichotomy. You do not need
to fully understand the pattern now; you can take it as a black box.
-/

example (x1 x2 : ℝ) : x1 ≤ x2 ∨ x2 < x1 :=
begin
  rcases trichotomous_of (<) x1 x2 with h | h | h,
  { -- In this case, we have `h : x1 < x2`.
    left,
    apply le_of_lt h },
  { -- In this case, we have `h : x1 = x2`.
    left,
    rw h },
  -- In this case, we have `h : x2 < x1`
  right,
  exact h
end

open function

/-
Here is an example that shows that `x ↦ x + 1` is injective.
-/

example : injective (λ x, x + 1) :=
begin
  intros x1 x2 h,
  dsimp at h,  -- this makes `h` more readable
  exact add_right_cancel h,
end

/-
Show that every strictly monotone function is injective.
-/

theorem injective_of_strict_mono (hf : strict_mono f) : injective f :=
begin
  unfold injective,
  intros a b h,
  by_contra h₀,
  rcases trichotomous_of (<) a b with alb | aeqb | bla,
  have falfb : f a < f b,
  {apply hf alb,
  },
  linarith,
  apply h₀ aeqb,
  have fblfa : f b < f a,
  {apply hf bla,
  },
  linarith,
end

end strict_mono_exercise

/-
SECOND EXERCISE: Galois connections

Given `α` with a partial order, a *closure operator* `cl : α → α` has the
following properties:

- `cl` is monotone
- `cl` is increasing, in the sense that for every `a : α`, `a ≤ cl a`
- `cl` is idempotent, in the sense that for every `a : α`, `cl (cl a) = cl a`.

Given `α` and `β` with partial orders, a *Galois connection* is a pair of
monotone functions `f : α → β` and `g : β → α` satisfying the following:

  For every `a` and `b`, `f a ≤ b` if and only if `a ≤ g b`.

You can read more about these here:

  https://en.wikipedia.org/wiki/Closure_operator
  https://en.wikipedia.org/wiki/Galois_connection

The exercises below ask you to show that if `f` and `g` form a Galois
connection, then `g ∘ f` is a closure operator, and `f ∘ g` is a closure
operator on the reverse order.
-/

namespace galois_connection_exercise

variables {α β : Type*} [partial_order α] [partial_order β]
variable  {f : α → β}
variable  {g : β → α}
variable  mono_f : monotone f
variable  mono_g : monotone g
variable  adj1 : ∀ a b, f a ≤ b → a ≤ g b
variable  adj2 : ∀ a b, a ≤ g b → f a ≤ b

section
-- you can use these:
include mono_f mono_g

theorem mono_gf : monotone (g ∘ f) :=
begin
  unfold monotone,
  dsimp,
  intros a b aleqb,
  have faleqfb : f a ≤ f b,
  {apply mono_f aleqb,
  },
  apply mono_g faleqfb,
end

theorem mono_fg : monotone (f ∘ g) :=
begin
  intros a b aleqb,
  have galeqgb : g a ≤ g b,
  {apply mono_g aleqb,
  },
  apply mono_f galeqgb,
end

end

section
include adj1

theorem increasing_gf : ∀ a, a ≤ g (f a) :=
begin
  intro a,
  have h : f a ≤ f a → a ≤ g (f a),
  {exact adj1 a (f a),
  },
  have faleqfa : f a ≤ f a,
  {apply rfl.ge,
  },
  apply h faleqfa,
end
end

section
include adj2

theorem decreasing_fg : ∀ b, f (g b) ≤ b :=
begin
  intro b,
  have h : g b ≤ g b → f (g b) ≤ b,
  {exact adj2 (g b) b,
  },
  have gbleqgb : g b ≤ g b,
  {apply rfl.ge,
  },
  apply h gbleqgb,
end
end

include mono_f mono_g adj1 adj2

/-
Unfortunately, for the theorems you just proved, you have to give the
hypotheses as arguments.
-/

#check mono_fg mono_f mono_g
#check mono_gf mono_f mono_g
#check increasing_gf adj1
#check decreasing_fg adj2

theorem idempotent_gf : ∀ a, g (f (g (f a))) = g (f a) :=
begin
  intro a,
  apply le_antisymm,
  have h0 : f (g (f (g (f a)))) ≤ f a → g (f (g (f a))) ≤ g (f a),
  {exact adj1 (g (f (g (f a)))) (f a),
  },
  have h1 : (f (g (f a))) ≤ f a,
  {exact decreasing_fg adj2 (f a),
  },
  have h2 : f (g (f (g (f a)))) ≤ f (g (f a)),
  {exact decreasing_fg adj2 (f (g (f a))),
  },
  have h3 : f (g (f (g (f a)))) ≤ f a,
  {apply le_trans h2 h1,
  },
  apply h0 h3,
  have h0 : f (g (f a)) ≤ f (g (f a)) → g (f a) ≤ g (f (g (f a))),
  {exact adj1 (g (f a)) (f (g (f a))),
  },
  have h1 : f (g (f a)) ≤ f (g (f a)),
  {apply rfl.ge,
  },
  apply h0 h1,
end

theorem idempotent_fg : ∀ b, f (g (f (g b))) = f (g b) :=
begin
  intro b,
  apply le_antisymm,
  have h0 : g (f (g b)) ≤ g (f (g b)) → f (g (f (g b))) ≤ f (g b),
  {exact adj2 (g (f (g b))) (f (g b)),
  },
  have h1 : g (f (g b)) ≤ g (f (g b)),
  {apply rfl.ge,
  },
  apply h0 h1,
  have h0 : g b ≤ g (f (g (f (g b)))) → f (g b) ≤ f (g (f (g b))),
  {exact adj2 (g b) (f (g (f (g b)))),
  },
  have h1 : g b ≤ g (f (g b)),
  {exact increasing_gf adj1 (g b),
  },
  have h2 : g (f (g b)) ≤ g (f (g (f (g b)))),
  {exact increasing_gf adj1 (g (f (g b))),
  },
  have h3 : g b ≤ g (f (g (f (g b)))),
  {apply le_trans h1 h2,
  },
  apply h0 h3,
end

end galois_connection_exercise

/-
THIRD EXERCISE: convergence to infinity

Below, `to_infinity f` expresses that `f x` approaches infinity as
`x` approaches infinity.

The properties below are analogous to properties proved in Sections 3.2
and 3.6 in Mathematics in Lean. They involve the universal and existential
quantifiers (both no other logical connectives).
-/

def to_infinity (f : ℝ → ℝ) := ∀ b, ∃ x₀, ∀ x, x₀ ≤ x → b < f x

-- hint: you can use `linarith` at the end
theorem to_infinity_add_constant (f : ℝ → ℝ) (r : ℝ) (hf : to_infinity f) :
  to_infinity (λ x, f x  + r) :=
begin
  unfold to_infinity,
  unfold to_infinity at hf,
  intro b,
  specialize hf (b - r),
  cases hf with x₀ hx0,
  use x₀,
  intro x,
  intro hx,
  specialize hx0 x,
  have h : b - r < f x,
  {apply hx0 hx,
  },
  exact sub_lt_iff_lt_add.mp (hx0 hx),
end

-- hint: `div_lt_iff'` is useful here
theorem scaling_to_infinity (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hf : to_infinity f) :
  to_infinity (λ x, r * f x) :=
begin
  unfold to_infinity,
  unfold to_infinity at hf,
  intro b,
  specialize hf (b / r),
  cases hf with x₀ hx0,
  use x₀,
  intro x,
  intro hx,
  specialize hx0 x,
  have h : b / r < f x,
  {apply hx0 hx,
  },
  exact (div_lt_iff' hr).mp (hx0 hx),
end

-- hint: you can use `le_max_left` and `le_max_right`
theorem sum_of_to_infinity (f g : ℝ → ℝ) (hf : to_infinity f) (hg : to_infinity g) :
  to_infinity (f + g) :=
begin
  unfold to_infinity,
  unfold to_infinity at hf,
  unfold to_infinity at hg,
  intro b,
  specialize hf (b / 2),
  specialize hg (b / 2),
  cases hf with x₀ hx0,
  cases hg with x₁ hx1,
  let xmax := max x₀ x₁,
  use xmax,
  intro x,
  intro h,
  specialize hx0 x,
  specialize hx1 x,
  let maxl := le_max_left x₀ x₁,
  let maxr := le_max_right x₀ x₁,
  have x0lex : x₀ ≤ x,
  {apply le_trans maxl h,
  },
  have x1lex : x₁ ≤ x,
  {apply le_trans maxr h,
  },
  have blfx : b / 2 < f x,
  {apply hx0 x0lex,
  },
  have blgx : b / 2 < g x,
  {apply hx1 x1lex,
  },
  have blfxgx : b / 2 + b / 2 < f x + g x,
  {apply add_lt_add blfx blgx,
  },
  have halfplus : b / 2 + b / 2 = b,
  {ring,},
  rw halfplus at blfxgx,
  exact blfxgx,
end