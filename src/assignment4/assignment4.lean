import data.real.basic

/-
EXERCISE 1.

Prove the following without using automation, i.e. only with basic tactics
such as `intros`, `apply`, `split`, `cases`, `left`, `right`, and `use`.
-/

section

variables {α β : Type} (p q : α → Prop) (r : α → β → Prop)

-- Exercise 1a. [10pts]
example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x :=
begin
  intro h,
  intro x,
  cases h with hl hr,
  specialize hl x,
  specialize hr x,
  split,
  exact hl,
  exact hr,
end

-- Exercise 1b. [10pts]
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
  intro h,
  intro x,
  cases h with hl hr,
  specialize hl x,
  left,
  exact hl,
  specialize hr x,
  right,
  exact hr,
end

-- Exercise 1c. [10pts]
example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y :=
begin
  intro h,
  intro y,
  cases h with x hx,
  specialize hx y,
  use x,
  exact hx,
end

end

/-
EXERCISE 2.

Suppose two pairs of real numbers {a, b} and {c, d} have the same sum
and product. The following theorem shows that either a = c and b = d,
or a = d and b = c. Fill in the details. You can use `ring`, `ring_nf`
and `linarith` freely.
-/

-- Exercise 2. [20pts]
theorem sum_product_magic (a b c d : ℝ)
    (sumeq : a + b = c + d) (prodeq : a * b = c * d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
begin
  have : (a - c) * (a - d) = 0,
  { have r : b = c + d - a,
    linarith,
    rw r at prodeq,
    linarith,
  },
  have := eq_zero_or_eq_zero_of_mul_eq_zero this,
  cases this with h h,
  { left,
    split,
    linarith,
    have r : a - c = d - b,
    {linarith,},
    rw h at r,
    linarith,
  },
  { by_cases ac : a = c,
    { left,
      split,
      exact ac,
      rw ac at sumeq,
      apply add_left_cancel sumeq,
    },
    { right,
      split,
      linarith,
      have ad : a = d,
      {linarith,},
      rw ad at sumeq,
      have r : d + b = d + c,
      {linarith,},
      apply add_left_cancel r,
    },
  }
end

/-
EXERCISE 3.

The predicate `approaches_at f b a` should be read "f(x) approaches b as x
approaches a", and the predicate `continuous f` says that f is continuous.

Prove the following two theorems.

Note that bounded quantification such as `∀ ε > 0, ..` really means `∀ ε, ε > 0 → ..`
and `∃ δ > 0, ..` really means `∃ δ, δ > 0 ∧ ..`.
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

-- Exercise 3a. [10pts]
theorem approaches_at_add_right  {f : ℝ → ℝ} {a b c: ℝ}
    (hf : approaches_at f b a) :
  approaches_at (λ x, f x + c) (b + c) a :=
begin
  unfold approaches_at,
  unfold approaches_at at hf,
  intros ε εpos,
  specialize hf ε,
  specialize hf εpos,
  cases hf with δ hf,
  cases hf with H hf,
  use δ,
  split,
  exact H,
  intro x,
  specialize hf x,
  intro h,
  ring_nf,
  specialize hf h,
  exact hf,  
end

-- Exercise 3b. [10pts]
theorem approaches_at_comp {f g : ℝ → ℝ} {a b c : ℝ}
  (hf : approaches_at f b a) (hg : approaches_at g c b) :
    approaches_at (g ∘ f) c a :=
begin
  unfold approaches_at,
  unfold approaches_at at hf,
  unfold approaches_at at hg,
  intros ε εpos,
  specialize hg ε,
  specialize hg εpos,
  cases hg with δg hg,
  cases hg with Hg hg,
  specialize hf δg,
  specialize hf Hg,
  cases hf with δf hf,
  cases hf with Hf hf,
  use δf,
  split,
  exact Hf,
  intro x,
  specialize hf x,
  specialize hg (f x),
  intro h,
  dsimp,
  specialize hf h,
  specialize hg hf,
  exact hg,
end

def continuous (f : ℝ → ℝ) := ∀ x, approaches_at f (f x) x

-- Exercise 3c. [10pts]
theorem continuous_add_right {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (λ x, f x + r) :=
begin
  unfold continuous,
  unfold approaches_at,
  unfold continuous at ctsf,
  unfold approaches_at at ctsf,
  intros x ε εpos,
  specialize ctsf x ε εpos,
  cases ctsf with δ ctsf,
  cases ctsf with H ctsf,
  use δ,
  split,
  exact H,
  intro x₀,
  specialize ctsf x₀,
  intro h,
  ring_nf,
  specialize ctsf h,
  exact ctsf,     
end

-- Since `f x - r` is the same as `f x + (- r)`, the following is an instance
-- of the previous theorem.
theorem continuous_sub {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (λ x, f x - r) :=
continuous_add_right ctsf (-r)

/-
EXERCISE 4.

In class, I will prove the intermediate value theorem in the form `ivt`.
Use that version to prove the more general one that comes after.
-/

/- We'll do this in class! You don't have to prove it,
   and you can leave the `sorry` and apply the theorem 
   as a black box. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
begin
  let S := {x : ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0 },
  have ainS : a ∈ S,
  { dsimp,
    exact ⟨le_refl a, aleb, hfa ⟩,  
  },
  
  have bddS : bdd_above S,
  { unfold bdd_above,
    use b,
    intros s sinS,
    exact sinS.2.1,
  },
  have Sfull : S.nonempty,
  { 
  use a,
  exact ainS,
  },
  set c:=  Sup S with cdef,
  have cleb : c ≤ b,
  { apply cSup_le Sfull,
    intros s sinS,
    exact sinS.2.1,
  },
  have alec : a ≤ c,
  { apply le_cSup bddS,
  exact ainS,
  },
  rcases trichotomous_of (<) (f c) 0 with h | h | h,
  {-- case where f c < 0 --going for a contradiction 
    exfalso, -- turn the contradiction into false
    specialize ctsf c,
    set ε := -f c / 2 with εdef,
    have εpos : ε > 0,
    {linarith,},
    specialize ctsf ε εpos,
    cases ctsf with δ ctsf,
    cases ctsf with δpos hδ,
    -- We need to check that c+δ/2 is in S
    by_cases c + δ/2 > b,
    { have bnearc : |b - c| < δ,
      { rw abs_lt,
        split,
        linarith,
        linarith,
      },
      specialize hδ b,
      specialize hδ bnearc,
      rw abs_lt at hδ,
      linarith, --deduces false from the inequality   
    },
    push_neg at h,
    --now in the case where c+δ/2 ≤ b,
    have c2nearc : |c + δ/2 - c| < δ,
    { simp, --cant actually use,
      rw abs_lt,
      split,
      linarith,
      linarith,
    }, 
    specialize hδ (c + δ/2) c2nearc,
    rw abs_lt at hδ,
    have : f (c + δ/2) < 0,
    {linarith,},
    by_cases c + δ/2 > b,
    {linarith,},
    push_neg at h,
    have c2lec : c + δ/2 ≤ c,
    {sorry,},
    sorry,
    },  
  {--case where f c = 0
  sorry,
  },
  sorry,
  --case where 0 < f c --also for a contrdiction-/
end

-- Use `ivt` to prove `ivt'` below.

-- Exercise 4. [20pts]
theorem ivt' {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c :=
begin
  let g := λ x, f x - c,
  have : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0,
  { have gbpos : g b > 0,
    {exact sub_pos.mpr hfb},
    have ganeg : g a < 0,
    {exact sub_neg.mpr hfa,},
    have ctsg : continuous g,
    {exact continuous_sub ctsf c,},
    apply ivt aleb ctsg ganeg gbpos,
  },
  dsimp [g] at this,
  cases this with x h,
  use x,
  cases h with h1 h2,
  cases h2,
  split,
  exact h1,
  split,
  exact h2_left,
  exact sub_eq_zero.mp h2_right,
end
