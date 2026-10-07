module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Preorder-Indexed Inverse Systems

This leaf provides the elementary vocabulary for an inverse system indexed by
a preorder: its transition maps and its restrictions to upper tails. It is
independent of limits, additive structure, and triangulated categories.
-/

universe uI vI uA vA

namespace CategoryTheory

/-- An inverse system indexed by a preorder `I`, with arrows directed from larger indices to
smaller indices. -/
abbrev PreorderInverseSystem (I : Type uI) [Preorder I] (A : Type uA) [Category.{vA} A] :=
  Iᵒᵖ ⥤ A

/-- An inverse system written as a functor from the order-dual category `OrderDual I`.

This is definitionally distinct from `PreorderInverseSystem I A = Iᵒᵖ ⥤ A`, and is the
representation used by the project for directed diagrams such as `OrderDual ℕ+ ⥤ A`. -/
abbrev OrderDualInverseSystem (I : Type uI) [Preorder I] (A : Type uA) [Category.{vA} A] :=
  OrderDual I ⥤ A

namespace PreorderInverseSystem

section

variable {I : Type uI} [Preorder I]
variable {A : Type uA} [Category.{vA} A]

/-- The transition map from a later stage to an earlier stage of a preorder-indexed inverse
system. -/
abbrev transitionMap (F : PreorderInverseSystem I A) {i j : I} (hij : i ≤ j) :
    F.obj (Opposite.op j) ⟶ F.obj (Opposite.op i) :=
  F.map (homOfLE hij).op

/-- Transition maps compose through every intermediate stage. -/
theorem transitionMap_comp (F : PreorderInverseSystem I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := sorry

/-- Restrict a preorder-indexed inverse system to the upper tail starting at `i`. -/
abbrev tail (F : PreorderInverseSystem I A) (i : I) :
    PreorderInverseSystem (Set.Ici i) A :=
  (OrderHom.Subtype.val (Set.Ici i)).toFunctor.op ⋙ F

end

end PreorderInverseSystem

namespace OrderDualInverseSystem

section

variable {I : Type uI} [Preorder I]
variable {A : Type uA} [Category.{vA} A]

/-- The transition map from stage `j` to stage `i` of an `OrderDual`-indexed inverse system,
for an ordinary inequality `i ≤ j`. -/
abbrev transitionMap (F : OrderDualInverseSystem I A) {i j : I} (hij : i ≤ j) :
    F.obj (OrderDual.toDual j) ⟶ F.obj (OrderDual.toDual i) :=
  F.map (homOfLE (OrderDual.toDual_le_toDual.mpr hij))

/-- Transition maps of an `OrderDual`-indexed inverse system compose through every intermediate
stage. -/
theorem transitionMap_comp (F : OrderDualInverseSystem I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := sorry

/-- The reflexive transition map of an `OrderDual`-indexed inverse system is the identity. -/
@[simp]
theorem transitionMap_refl (F : OrderDualInverseSystem I A) (i : I) :
    F.transitionMap (le_refl i) = 𝟙 (F.obj (OrderDual.toDual i)) := sorry

end

end OrderDualInverseSystem

end CategoryTheory
