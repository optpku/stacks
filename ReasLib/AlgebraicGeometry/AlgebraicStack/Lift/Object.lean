/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening

/-!
# Objects of the category of lifts of algebraic stacks

A lift object is a cartesian square of algebraic spaces over a thickening of
algebraic stacks, with an étale map to a fixed smooth algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- A lift along a thickening of algebraic stacks consists of algebraic spaces
`U`, `U'`, maps `a`, `i`, `x'`, and an invertible square cell, with `a` étale,
`x'` smooth, and the square a 2-fibre product. -/
def Object {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    Type (u + 1) :=
  Σ (U U' : AlgebraicSpace S) (a : U ⟶ W) (i : U ⟶ U')
    (x' : U'.toGroupoids ⟶ X'),
    { α : (AlgebraicSpace.toGroupoids.map a ≫ x) ≫ iX ≅
        AlgebraicSpace.toGroupoids.map i ≫ x' //
      AlgebraicSpace.Etale a ∧ Groupoids.Hom.Smooth x' ∧
        PseudoPullbackCone.IsBilimit (⟨U.toGroupoids,
          AlgebraicSpace.toGroupoids.map a ≫ x, AlgebraicSpace.toGroupoids.map i, α⟩ :
          PseudoPullbackCone iX x') }

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable {iX : X ⟶ X'} [IsThickening iX]
variable {W : AlgebraicSpace S} {x : W.toGroupoids ⟶ X}
variable [Groupoids.Hom.Smooth x]

namespace Object

/-- Package supplied spaces, maps, an invertible square cell, and the étale,
smooth, and cartesian conditions as a lift object. -/
def of (U U' : AlgebraicSpace S) (a : U ⟶ W) (i : U ⟶ U')
    (x' : U'.toGroupoids ⟶ X')
    (α : (AlgebraicSpace.toGroupoids.map a ≫ x) ≫ iX ≅
      AlgebraicSpace.toGroupoids.map i ≫ x')
    (etale : AlgebraicSpace.Etale a) (smooth : Groupoids.Hom.Smooth x')
    (isPullback : PseudoPullbackCone.IsBilimit (⟨U.toGroupoids,
      AlgebraicSpace.toGroupoids.map a ≫ x, AlgebraicSpace.toGroupoids.map i, α⟩ :
      PseudoPullbackCone iX x')) : Object iX x :=
  ⟨U, U', a, i, x', α, etale, smooth, isPullback⟩

/-- The algebraic space étale over the fixed smooth algebraic space. -/
def U (ξ : Object iX x) : AlgebraicSpace S := ξ.1

/-- The algebraic space mapping smoothly to the thickened stack. -/
def U' (ξ : Object iX x) : AlgebraicSpace S := ξ.2.1

/-- The étale map from the source space to the fixed algebraic space. -/
def a (ξ : Object iX x) : ξ.U ⟶ W := ξ.2.2.1

/-- The map between the two spaces in the cartesian square. -/
def i (ξ : Object iX x) : ξ.U ⟶ ξ.U' := ξ.2.2.2.1

/-- The smooth map from the target space to the thickened stack. -/
def x' (ξ : Object iX x) : ξ.U'.toGroupoids ⟶ X' := ξ.2.2.2.2.1

/-- The invertible cell witnessing commutativity of the lift square. -/
def α (ξ : Object iX x) :
    (AlgebraicSpace.toGroupoids.map ξ.a ≫ x) ≫ iX ≅
      AlgebraicSpace.toGroupoids.map ξ.i ≫ ξ.x' := ξ.2.2.2.2.2.1

/-- The map to the fixed algebraic space is étale. -/
theorem etale (ξ : Object iX x) : AlgebraicSpace.Etale ξ.a := ξ.2.2.2.2.2.2.1

/-- The map to the thickened stack is smooth. -/
theorem smooth (ξ : Object iX x) : Groupoids.Hom.Smooth ξ.x' := ξ.2.2.2.2.2.2.2.1

/-- The square stored by a lift object is a 2-fibre product. -/
theorem isPullback (ξ : Object iX x) :
    PseudoPullbackCone.IsBilimit (⟨ξ.U.toGroupoids,
      AlgebraicSpace.toGroupoids.map ξ.a ≫ x, AlgebraicSpace.toGroupoids.map ξ.i, ξ.α⟩ :
      PseudoPullbackCone iX ξ.x') := ξ.2.2.2.2.2.2.2.2

variable (iX x)

/-- Package algebraic spaces, maps, and a square cell with inferred étaleness
and smoothness and a supplied cartesian condition as a lift object. -/
def mk (U U' : AlgebraicSpace S) (a : U ⟶ W) (i : U ⟶ U')
    (x' : U'.toGroupoids ⟶ X')
    (α : (AlgebraicSpace.toGroupoids.map a ≫ x) ≫ iX ≅
      AlgebraicSpace.toGroupoids.map i ≫ x')
    [AlgebraicSpace.Etale a] [Groupoids.Hom.Smooth x']
    (h : PseudoPullbackCone.IsBilimit (⟨U.toGroupoids, AlgebraicSpace.toGroupoids.map a ≫ x,
        AlgebraicSpace.toGroupoids.map i, α⟩ :
      PseudoPullbackCone iX x')) : Object iX x :=
  of U U' a i x' α inferInstance inferInstance h

/-- The 2-commutative square with apex `U.toGroupoids` associated to a lift object. -/
def cone (ξ : Object iX x) : PseudoPullbackCone iX ξ.x' :=
  ⟨ξ.U.toGroupoids, AlgebraicSpace.toGroupoids.map ξ.a ≫ x,
    AlgebraicSpace.toGroupoids.map ξ.i, ξ.α⟩

/-- A lift object is étale over the fixed space, smooth over the thickened stack,
2-commutative via its square cell, and 2-cartesian. -/
theorem spec (ξ : Object iX x) :
    AlgebraicSpace.Etale ξ.a ∧ Groupoids.Hom.Smooth ξ.x' ∧
      ξ.α = ξ.cone.iso ∧ PseudoPullbackCone.IsBilimit ξ.cone := sorry

/-- The map between the two algebraic spaces of a lift object is a thickening. -/
instance isThickening (ξ : Object iX x) : AlgebraicSpace.IsThickening ξ.i :=
  sorry

/-- The étale map of a lift object defines an object of the spaces-étale site. -/
def toSpacesEtale (ξ : Object iX x) : AlgebraicSpace.spacesEtaleSite W :=
  MorphismProperty.Over.mk ⊤ ξ.a ξ.etale

end Object

end AlgebraicGeometry.AlgebraicStack.Lift
