module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Map

/-!
# Base change for total conormal algebras of immersions of algebraic spaces

The canonical comparison `f^* C_{Z'/X',*} ⟶ C_{Z/X,*}` associated to a cartesian
square of immersions of algebraic spaces is locally surjective, and is an
isomorphism when the ambient morphism is flat.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']

/-- The canonical comparison `f^* C_{Z'/X',*} ⟶ C_{Z/X,*}` of a cartesian square of
immersions of algebraic spaces is locally surjective as a map of étale sheaves of
commutative rings. -/
instance map_isLocallySurjective_of_isPullback (sq : IsPullback f i i' g) :
    Sheaf.IsLocallySurjective (map sq.toCommSq).hom.right :=
  sorry

/-- Every homogeneous piece of the canonical conormal-algebra comparison of a cartesian
square of immersions of algebraic spaces is an epimorphism. -/
instance mapPiece_epi_of_isPullback (sq : IsPullback f i i' g) (n : ℕ) :
    Epi (mapPiece sq.toCommSq n) :=
  sorry

/-- If the ambient morphism `g` is flat, the canonical comparison of total conormal
algebras associated to a cartesian square of immersions of algebraic spaces is an
isomorphism. -/
instance map_isIso_of_isPullback_of_flat [Flat g] (sq : IsPullback f i i' g) :
    IsIso (map sq.toCommSq : pullback f i' ⟶ total i) :=
  sorry

/-- If the ambient morphism is flat, the underlying commutative-ring sheaf map of the
canonical comparison is an isomorphism. -/
instance mapSheaf_isIso_of_isPullback_of_flat [Flat g] (sq : IsPullback f i i' g) :
    IsIso (mapSheaf sq.toCommSq) :=
  sorry

/-- If the ambient morphism is flat, every homogeneous piece of the canonical comparison
is an isomorphism. -/
instance mapPiece_isIso_of_isPullback_of_flat [Flat g] (sq : IsPullback f i i' g) (n : ℕ) :
    IsIso (mapPiece sq.toCommSq n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
