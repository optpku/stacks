module

public import stacks_project.Chap87.Lemma_87_37_6_Affine

/-!
# Countably indexed affine formal algebraic spaces, functor of points

The sequential affine presentation API is supplied by its mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine :
    ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine.of :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsAffine X]
    (D : ℕ ⥤ Over S) (h : IsDirectedAffineThickeningColimit D X),
    IsCountablyIndexedAffine X)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine.spec :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsCountablyIndexedAffine X],
    IsAffine X ∧ ∃ D : ℕ ⥤ Over S, IsDirectedAffineThickeningColimit D X)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine.iff :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u),
    IsCountablyIndexedAffine X ↔
      IsAffine X ∧ ∃ D : ℕ ⥤ Over S, IsDirectedAffineThickeningColimit D X)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine.instYoneda :
    ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left],
    IsCountablyIndexedAffine (yoneda.obj U))

end AlgebraicGeometry.AffineFormalAlgebraicSpace
