module

public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Affine formal algebraic spaces

An affine formal algebraic space over `S` is a directed affine thickening
colimit of schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A functor of points on schemes over `S` is an affine formal algebraic space
when it is a directed affine thickening colimit. -/
class IsAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a directed diagram of affine thickenings whose Yoneda colimit is
  isomorphic to `X`. -/
  exists_diagram :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X

namespace IsAffine

/-- The representable functor of an affine scheme over `S` is an affine formal
algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S) [AlgebraicGeometry.IsAffine U.left] :
    IsAffine (yoneda.obj U) :=
  sorry

/-- An affine formal algebraic space is a directed affine thickening colimit. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X :=
  sorry

/-- Affine formal algebraic spaces are exactly directed affine thickening
colimits. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsAffine X ↔
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X :=
  sorry

end IsAffine

end AlgebraicGeometry.FormalAlgebraicSpace
