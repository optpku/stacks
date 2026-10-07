module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap106.Definition_106_3_1_Thickening

/-!
# Objects of the category of lifts of algebraic stacks

An object of the category of lifts along a thickening of algebraic stacks is a
system of algebraic spaces and maps forming a 2-cartesian square over the
thickening, with an étale map to the given algebraic space and a smooth map
from the thickened space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable (iX : X ⟶ X') [IsThickening iX]
variable {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
variable [Groupoids.Hom.Smooth x]

/-- An object of the category of lifts along a thickening `iX : X ⟶ X'` and a
smooth map `x : W.toGroupoids ⟶ X` is a system `(U, U', a, i, x', α)` with
`a` étale, `x'` smooth, and `U` the 2-fibre product `X ×_{X'} U'`. -/
structure Object where
  /-- Package the spaces, maps, square 2-cell, and cartesian/étale/smooth
  conditions as an object of the category of lifts. -/
  of ::
  /-- The algebraic space `U` étale over `W`. -/
  U : AlgebraicSpace S
  /-- The algebraic space `U'` smooth over `X'`. -/
  U' : AlgebraicSpace S
  /-- The étale morphism `a : U ⟶ W`. -/
  a : U ⟶ W
  /-- The morphism `i : U ⟶ U'` of algebraic spaces. -/
  i : U ⟶ U'
  /-- The smooth 1-morphism `x' : U'.toGroupoids ⟶ X'`. -/
  x' : U'.toGroupoids ⟶ X'
  /-- The square 2-cell `α` witnessing `x ∘ a` then `iX` isomorphic to `x' ∘ i`. -/
  α : (AlgebraicSpace.toGroupoids.map a ≫ x) ≫ iX ≅
      AlgebraicSpace.toGroupoids.map i ≫ x'
  /-- The morphism `a : U ⟶ W` is étale. -/
  etale : AlgebraicSpace.Etale a
  /-- The 1-morphism `x' : U'.toGroupoids ⟶ X'` is smooth. -/
  smooth : Groupoids.Hom.Smooth x'
  /-- The square is a 2-fibre product: `U = X ×_{X'} U'`. -/
  isPullback :
    PseudoPullbackCone.IsBilimit (⟨U.toGroupoids, AlgebraicSpace.toGroupoids.map a ≫ x,
        AlgebraicSpace.toGroupoids.map i, α⟩ :
      PseudoPullbackCone iX x')

namespace Object

/-- Package algebraic spaces `U`, `U'`, maps `a`, `i`, `x'`, and the square
2-cell `α` as an object of the category of lifts. -/
def mk (U U' : AlgebraicSpace S) (a : U ⟶ W) (i : U ⟶ U')
    (x' : U'.toGroupoids ⟶ X')
    (α : (AlgebraicSpace.toGroupoids.map a ≫ x) ≫ iX ≅
      AlgebraicSpace.toGroupoids.map i ≫ x')
    [AlgebraicSpace.Etale a] [Groupoids.Hom.Smooth x']
    (h : PseudoPullbackCone.IsBilimit (⟨U.toGroupoids, AlgebraicSpace.toGroupoids.map a ≫ x,
        AlgebraicSpace.toGroupoids.map i, α⟩ :
      PseudoPullbackCone iX x')) : Object iX x :=
  of U U' a i x' α inferInstance inferInstance h

/-- The readable 2-commutative square with apex `U.toGroupoids` associated to a
lift object. -/
def cone (ξ : Object iX x) : PseudoPullbackCone iX ξ.x' :=
  ⟨ξ.U.toGroupoids, AlgebraicSpace.toGroupoids.map ξ.a ≫ x,
    AlgebraicSpace.toGroupoids.map ξ.i, ξ.α⟩

/-- An object of the category of lifts is étale over `W`, smooth over `X'`,
2-commutative via its square cell, and 2-cartesian. -/
theorem spec (ξ : Object iX x) :
    AlgebraicSpace.Etale ξ.a ∧ Groupoids.Hom.Smooth ξ.x' ∧
      ξ.α = ξ.cone.iso ∧ PseudoPullbackCone.IsBilimit ξ.cone := sorry

/-- In particular the morphism `i : U ⟶ U'` of a lift object is a thickening
of algebraic spaces. -/
theorem isThickening (ξ : Object iX x) : AlgebraicSpace.IsThickening ξ.i :=
  sorry

/-- The étale map `a : U ⟶ W` of a lift object, as an object of
`W_spaces,étale`. -/
def toSpacesEtale (ξ : Object iX x) : AlgebraicSpace.spacesEtaleSite W :=
  MorphismProperty.Over.mk ⊤ ξ.a ξ.etale

end Object

end AlgebraicGeometry.AlgebraicStack.Lift
