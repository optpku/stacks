module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_5_3_Map

/-!
# Base change for conormal sheaves of immersions of algebraic spaces

The canonical comparison `f^* C_{Z'/X'} ⟶ C_{Z/X}` associated to a cartesian
square of immersions of algebraic spaces is an epimorphism, and is an
isomorphism when the ambient morphism is flat.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']

/-- The canonical comparison `f^* C_{Z'/X'} ⟶ C_{Z/X}` of a cartesian square of
immersions of algebraic spaces is an epimorphism. -/
instance map_epi_of_isPullback (sq : IsPullback f i i' g) :
    Epi (map sq.toCommSq) :=
  sorry

/-- If the ambient morphism `g` is flat, the canonical comparison of conormal
sheaves associated to a cartesian square of immersions of algebraic spaces is an
isomorphism. -/
instance map_isIso_of_isPullback_of_flat [Flat g] (sq : IsPullback f i i' g) :
    IsIso (map sq.toCommSq) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
