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
(elements: set α)

--Then, we define a subgroup H of G (same group axioms as above with some additional properties)
class subgroup (α : Type*) :=
(mul: α → α → α)
(e: α)
(inv: α → α)
(mul_assoc: ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_identity: ∀ x : α, mul x e = x)
(identity_mul: ∀ x : α, mul e x = x)
(elements: set α)
axiom subgroup_subset {α : Type*} [mygroup α] (H : subgroup α) : H.elements ⊆ mygroup.elements
axiom subgroup_nonempty {α : Type*} (H : subgroup α) : ∃ x : α, x ∈ H.elements
axiom subgroup_closedproducts {α : Type*} (H : subgroup α) : ∀ x y : α, x ∈ H.elements → y ∈ H.elements → H.mul x y ∈ H.elements

--Then, we define the binary relation
class myequivalence (α : Type*) :=
(R: α → α → Prop)
(refl: ∀ x : α, R x x)
(symm: ∀ x y : α, R x y → R y x)
(trans: ∀ x y z : α, R x y → R y z → R x z)

--Specifying it in the context of groups when it is induced by subgroup:
--Def (Equivalence relation induced by a subgroup): Let G be a group, and H ≤ G a subgroup of G. For a,b ∈ G, we say R a b iff ∃ h ∈ H such that a = bh, i.e. b⁻¹a ∈ H.
def subgroup_relation {α : Type*} [mygroup α] (H : subgroup α) (a b : α) : Prop :=
∃ h : α , h ∈ H.elements ∧ (a = H.mul b h ∨ H.mul (H.inv b) a ∈ H.elements)    

--Then, we prove that the binary relation is an equivalence relation on G
def subgroup_equivalence {α : Type*} [mygroup α] (H : subgroup α) : myequivalence α :=
{
  R := sorry,
  refl := sorry,
  symm := sorry,
  trans := sorry,
}

--Then, we define the left coset of H
--Def (Equivalence class of g) = {x ∈ G | R x g}  
def left_coset {α : Type*} [mygroup α] (H : subgroup α) (g : α) : set α :=
sorry

--Then, show that if e is the identity element of G, it is also the identity element of H

--Then, we show that every element of G is in some coset of H

--Then, show that any two distinct left cosets of H are disjoint


--Then, show the union of the left cosets of H is equal to G
