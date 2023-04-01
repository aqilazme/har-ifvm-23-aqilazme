import tactic
import data.set


--Proposition: "Let H be any subgroup of the group G.
--The set of the left cosets of H form a partition of G".
--Reference: Proposition 4, Dummit's Abstract Algebra (Third Edition) pg. 80
--Reference of the proof: http://mathonline.wikidot.com/the-set-of-left-right-cosets-of-a-subgroup-partitions-the-wh


--First, we define the group G along with the main group axioms:
class mygroup (α : Type*) :=
(mul: α → α → α)
(e: α)
(inv: α → α)
(mul_assoc: ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_identity: ∀ x : α, mul x e = x)
(identity_mul: ∀ x : α, mul e x = x)
(mul_inverse: ∀ x : α, mul x (inv x) = e)
(inverse_mul: ∀ x : α, mul (inv x) x = e)
(inv_inv: ∀ x : α, inv (inv x) = x)
(elements: set α)
axiom group_nonempty {α : Type*} (G : mygroup α) : ∃ x : α, x ∈ G.elements
axiom group_identity_member {α : Type*} (G : mygroup α) : G.e ∈ G.elements
axiom group_closedproducts {α : Type*} (G : mygroup α) : ∀ x y : α, x ∈ G.elements → y ∈ G.elements → G.mul x y ∈ G.elements

lemma mygroup.right_cancel {α : Type*} [mygroup α] (G : mygroup α) (x y z : α) (h : G.mul y x = G.mul z x) : y = z :=
begin
  have h1 : G.mul y (G.mul x (G.inv x)) = G.mul z (G.mul x (G.inv x)),
  { rw ←G.mul_assoc,
    rw h,
    rw G.mul_assoc,
  },
  rw G.mul_inverse at h1,
  rw G.mul_identity at h1,
  rw G.mul_identity at h1,
  exact h1,
end

--With the way Lean syntax works, sometimes I need a statement like x ∈ G.elements explicitly, which Lean can't infer on its own even if we have x : α, and have defined above that G.elements : set α
--This makes the definition explicit
axiom member_of_group {α :Type*} [mygroup α] (G : mygroup α) : ∀ x : α, x ∈ G.elements     

--Then, we define a subgroup H of G (same group axioms as above with some additional properties)
class subgroup (α : Type*) :=
(mul: α → α → α)
(e: α)
(inv: α → α)
(mul_assoc: ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_identity: ∀ x : α, mul x e = x)
(identity_mul: ∀ x : α, mul e x = x)
(mul_inverse: ∀ x : α, mul x (inv x) = e)
(inverse_mul: ∀ x : α, mul (inv x) x = e)
(inv_inv: ∀ x : α, inv (inv x) = x)
(elements: set α)
axiom subgroup_subset {α : Type*} [mygroup α] (H : subgroup α) : H.elements ⊆ mygroup.elements
axiom subgroup_nonempty {α : Type*} (H : subgroup α) : ∃ x : α, x ∈ H.elements
axiom subgroup_identity_member {α : Type*} (H : subgroup α) : H.e ∈ H.elements
axiom subgroup_closedproducts {α : Type*} (H : subgroup α) : ∀ x y : α, x ∈ H.elements → y ∈ H.elements → H.mul x y ∈ H.elements
--The subgroup H also inherits the same group operation in G
axiom subgroup_operations {α : Type*} [mygroup α] (G : mygroup α) (H : subgroup α) : ∀ x y : α, G.mul x y = H.mul x y 
axiom subgroup_inverses {α : Type*} [mygroup α] (G : mygroup α) (H : subgroup α) : ∀ x : α, x ∈ H.elements → H.inv x = G.inv x

lemma subgroup.right_cancel {α : Type*} (H : subgroup α) (x y z : α) (h : H.mul y x = H.mul z x) : y = z :=
begin
  have h1 : H.mul y (H.mul x (H.inv x)) = H.mul z (H.mul x (H.inv x)),
  { rw ←H.mul_assoc,
    rw h,
    rw H.mul_assoc,
  },
  rw H.mul_inverse at h1,
  rw H.mul_identity at h1,
  rw H.mul_identity at h1,
  exact h1,
end

lemma subgroup.right_mul {α : Type*} (H : subgroup α) : ∀ x y z : α , y = z →  H.mul y x = H.mul z x :=
begin
  intros x y z h,
  rw h,
end

lemma subgroup.left_mul {α : Type*} (H : subgroup α) : ∀ x y z : α , y = z →  H.mul x y  = H.mul x z :=
begin
  intros x y z h,
  rw h,
end

lemma subgroup.inverse_product {α : Type*} (H : subgroup α) (x y : α) (h : (H.mul x y) ∈ H.elements) : H.inv (H.mul x y) = H.mul (H.inv y) (H.inv x) :=
begin
  have h1 : H.mul (H.mul x y) (H.inv (H.mul x y)) = H.e,
  {
    rw H.mul_inverse,
  },
  have h2 : H.mul x (H.mul y (H.inv (H.mul x y))) = H.e,
  {
    simp [←H.mul_assoc],
    exact h1,
  },
  have h3: H.mul (H.inv x) (H.mul x (H.mul y (H.inv (H.mul x y)))) = H.mul (H.inv x) (H.e),
  {
    apply H.left_mul (H.inv x),
    exact h2,
  },
  have h4: H.mul (H.mul (H.inv x) x) (H.mul y (H.inv (H.mul x y))) = H.mul (H.inv x) (H.e),
  {
    simp [H.mul_assoc],
    exact h3,
  },
  have h5: H.mul (H.inv y) (H.mul (H.mul (H.inv x) x) (H.mul y (H.inv (H.mul x y)))) = H.mul (H.inv y) (H.mul (H.inv x) (H.e)),
  {
    apply H.left_mul (H.inv y),
    exact h4,
  },
  rw H.mul_identity at h5,
  rw H.inverse_mul at h5,
  rw H.identity_mul at h5,
  rw ←H.mul_assoc at h5,
  rw H.inverse_mul at h5,
  rw H.identity_mul at h5,
  exact h5,
end


--Then, we define the binary relation
class myequivalence (α : Type*) :=
(R: α → α → Prop)
(refl: ∀ x : α, R x x)
(symm: ∀ x y : α, R x y → R y x)
(trans: ∀ x y z : α, R x y → R y z → R x z)

--Specifying it in the context of groups when it is induced by subgroup:
--Def (Equivalence relation induced by a subgroup): Let G be a group, and H ≤ G a subgroup of G. For a,b ∈ G, we say R a b iff ∃ h ∈ H such that a = bh, (i.e. b⁻¹a ∈ H).
def subgroup_relation {α : Type*} [mygroup α] (H : subgroup α) (a b : α) : Prop :=
∃ h : α , (h ∈ H.elements ∧ (a = H.mul b h)) 

--Then, we prove that the binary relation is an equivalence relation on G
--It turns out that I need the obvious result that if h ∈ H, then h⁻¹ ∈ H 
axiom subgroup_inv_closed {α : Type*} [mygroup α] (H : subgroup α) (h : α) (h' : h ∈ H.elements): (H.inv h) ∈ H.elements

def subgroup_equivalence {α : Type*} [mygroup α] (H : subgroup α) : myequivalence α :=
{
  R := λ x y : α, subgroup_relation H x y,
  refl := 
    begin
      intro x,
      unfold subgroup_relation,
      use H.e,
      split,
      --show that a subgroup is nonempty i.e. there is at least one element in H
      cases subgroup_nonempty H with h h1,
      {
        have hinv : (H.inv h) ∈ H.elements,
        {
          apply subgroup_inv_closed,
          exact h1,
        },
        have h2 : H.mul h (H.inv h) ∈ H.elements,
        {
          apply subgroup_closedproducts H,
          exact h1,
          exact hinv,
        },
        have h3 : H.mul h (H.inv h) = H.e,
        {
          apply H.mul_inverse,
        },
        rw ←h3,
        exact h2,
      },
    rw H.mul_identity x,
    end,
  symm :=
    begin
      intros x y h1,
      unfold subgroup_relation,
      unfold subgroup_relation at h1,
      cases h1 with h h2,
      cases h2,
      cases h2_right,
      use (H.inv h),
      split,
      {
        apply subgroup_inv_closed,
        apply h2_left,
      },
      rw H.mul_assoc,
      rw H.mul_inverse,
      rw H.mul_identity,
    end,
  trans :=
  begin
    intros x y z h1 h2,
    unfold subgroup_relation at h1 h2,
    unfold subgroup_relation,
    cases h1 with h h1,
    cases h2 with k h2,
    use H.mul k h,
    split,
    {
      apply subgroup_closedproducts,
      exact h2.1,
      exact h1.1,
    },
   cases h1,
   cases h2,
   rw h2_right at h1_right,
   rw ←H.mul_assoc,
   exact h1_right,
  end
}

--Then, we define the left coset of H
--Def (Equivalence class of g) = {x ∈ G | R x g}  
def left_coset {α : Type*} [mygroup α] (g : α) (H : subgroup α) : set α :=
{x : α | subgroup_relation H x g}

--Then, show that if e is the identity element of G, it is also the identity element of H
lemma subgroup_identity {α : Type*} [mygroup α] (G : mygroup α) (H : subgroup α) : G.e = H.e :=
begin
  cases subgroup_nonempty H with subgroup.e h1,
  have h2 : subgroup.e ∈ G.elements,
  {
    apply subgroup_subset,
    exact h1,
  },
  cases subgroup_nonempty H with x h3, --i.e. take x as an arbitrary element in H
  have h4 : x ∈ G.elements,
  {
    apply subgroup_subset,
    exact h3,
  }, 
  have h4 : G.mul x (G.inv x) = G.e,
  {
    apply G.mul_inverse,
  },
  rw ←h4, 
  have h5 : H.mul x (H.inv x) = H.e,
  {
    rw H.mul_inverse,
  },
  rw ←h5,
  rw subgroup_operations,
  rw subgroup_inverses,
  exact h3,
end

--Then, we show that every element of G is in some coset of H
lemma group_elements_in_coset {α : Type*} (G : mygroup α) (H' : subgroup α) : ∀ x ∈ G.elements, ∃ g ∈ G.elements, x ∈ left_coset g H' :=
begin
  intros x Gx,
  --take an arbitrary element g in H
  cases subgroup_nonempty H' with g h1,
  have h2 : H'.inv g ∈ G.elements,
  {
    have h : H'.inv g ∈ H'.elements,
    {
      apply subgroup_inv_closed,
      exact h1,
    },
    apply subgroup_subset,
    exact h,
  },
  have h3 : G.mul x (H'.inv g) ∈ G.elements,
  {
    apply group_closedproducts,
    exact Gx,
    exact h2,
  },
  have h4 : x = G.mul (G.mul x (H'.inv g)) g,
  {
    rw G.mul_assoc,
    rw subgroup_inverses,
    rw G.inverse_mul,
    rw G.mul_identity,
    exact h1,
  },
  unfold left_coset,
  unfold subgroup_relation,
  use mygroup.mul x (subgroup.inv g),
  split,
  exact h3,
  use g,
  split,
  exact h1,
  rw ←subgroup_operations,
  exact h4,
end

--Then, show that any two distinct left cosets of H are disjoint
lemma disjoint_cosets {α : Type*} (G : mygroup α) (H : subgroup α) : ∀ (g₁ g₂ : α), g₁ ≠ g₂ → left_coset g₁ H ≠ left_coset g₂ H → left_coset g₁ H ∩ left_coset g₂ H = ∅ :=
begin
  intros g₁ g₂ g1neqg2 g1Hneqg2H,
  by_contradiction,
  rw set.eq_empty_iff_forall_not_mem at h,
  push_neg at h,
  cases h with x hx,
  rw set.mem_inter_iff at hx,
  cases hx with hg1 hg2,
  unfold left_coset at hg1,
  unfold left_coset at hg2,
  cases hg1 with h₁ h1g1,
  cases hg2 with h₂ h2g2,
  have h1 : H.mul g₁ h₁ = H.mul g₂ h₂,
  {
    cases h1g1,
    cases h2g2,
    rw h1g1_right at h2g2_right,
    exact h2g2_right,
  },
  have h2 : g₁ = H.mul g₂ (H.mul h₂ (H.inv h₁)),
  {
    rw ←H.mul_assoc,
    have h : H.mul (H.mul g₁ h₁) (H.inv h₁) = H.mul (H.mul g₂ h₂) (H.inv h₁),
    {
      apply H.right_mul (H.inv h₁),
      exact h1,
    },
    rw H.mul_assoc at h,
    rw H.mul_inverse at h,
    rw H.mul_identity at h,
    exact h,
  },
  have h3 : H.mul h₂ (H.inv h₁) ∈ H.elements,
  {
    apply subgroup_closedproducts,
    exact h2g2.1,
    have h : H.inv h₁ ∈ H.elements,
    {
      apply subgroup_inv_closed,
      exact h1g1.1,
    }, 
    exact h,
  }, 
  have h4 : g₂ = H.mul g₁ (H.mul h₁ (H.inv h₂)),
  {
    rw ←H.mul_assoc,
    have h : H.mul (H.mul g₁ h₁) (H.inv h₂) = H.mul (H.mul g₂ h₂) (H.inv h₂),
    {
      apply H.right_mul (H.inv h₂),
      exact h1,
    },
    rw H.mul_assoc at h,
    rw H.mul_assoc at h,
    rw H.mul_inverse at h,
    rw H.mul_identity at h,
    symmetry,
    rw ←H.mul_assoc at h, 
    exact h,
  },
  have h5 : H.mul h₁ (H.inv h₂) ∈ H.elements,
  {
    apply subgroup_closedproducts,
    exact h1g1.1,
    have h : H.inv h₂ ∈ H.elements,
    {
      apply subgroup_inv_closed,
      exact h2g2.1,
    }, 
    exact h,
  },
  have g1ing2H : g₁ ∈ left_coset g₂ H,
  {
    unfold left_coset,
    use H.mul h₂ (H.inv h₁),
    split,
    exact h3,
    exact h2,
  },
  have g2ing1H : g₂ ∈ left_coset g₁ H,
  {
    unfold left_coset,
    use H.mul h₁ (H.inv h₂),
    split,
    exact h5,
    exact h4,
  },
  have g1Hsubg2H : left_coset g₁ H ⊆ left_coset g₂ H,
  {
    intros x xing1H,
    cases g1ing2H with h g1ing2H,
    cases xing1H with h' xing1H,
    cases g1ing2H,
    rw g1ing2H_right at xing1H,
    use H.mul h h',
    split,
    have h : H.mul h h' ∈ H.elements,
    {
      apply subgroup_closedproducts,
      exact g1ing2H_left,
      exact xing1H.1,
    },
    exact h,
    cases xing1H,
    rw ←H.mul_assoc,
    exact xing1H_right,
  },
  have g2Hsubg1H : left_coset g₂ H ⊆ left_coset g₁ H,
  {
    intros x xing2H,
    cases g2ing1H with h g2ing1H,
    cases xing2H with h' xing2H,
    cases g2ing1H,
    rw g2ing1H_right at xing2H,
    use H.mul h h',
    split,
    have h : H.mul h h' ∈ H.elements,
    {
      apply subgroup_closedproducts,
      exact g2ing1H_left,
      exact xing2H.1,
    },
    exact h,
    cases xing2H,
    rw ←H.mul_assoc,
    exact xing2H_right,
  },
  have contra : left_coset g₁ H = left_coset g₂ H,
  {
    apply set.subset.antisymm,
    exact g1Hsubg2H,
    exact g2Hsubg1H,
  },
  contradiction,
end   

--Finally, show the union of the left cosets of H is equal to G
lemma union_left_cosets_eq_group {α : Type*} (G : mygroup α) (H : subgroup α) : (⋃ x : α, left_coset x H) = G.elements :=
begin
  ext,
  split,
  {
    intro h,
    cases h with s hs,
    simp at hs,
    cases hs,
    cases hs_left with y yH,
    unfold left_coset at yH,
    unfold subgroup_relation at yH,
    cases yH with h yH,
    rw ←yH at hs_right,
    rw set.mem_set_of_eq at hs_right,
    cases hs_right with h h1,
    cases h1 with hinH xyh,
    rw xyh,
    rw ←subgroup_operations G,
    have h1 : G.mul y h ∈ G.elements,
    {
      apply group_closedproducts,
      apply member_of_group,
      apply subgroup_subset,
      exact hinH,
    },
    exact h1,
  },
  intro h,
  simp,
  use x,
  unfold left_coset,
  unfold subgroup_relation,
  use H.e,
  split,
  {
    apply subgroup_identity_member,
  },
  rw H.mul_identity,
end