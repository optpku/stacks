module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.GroupScheme
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap95.Lemma_95_14_10_Torsors

/-!
# Group schemes as group algebraic spaces

A group scheme over `S` determines a group algebraic space over `S` viewed as an
algebraic space, so the classifying stack of fppf torsors from Examples of
Stacks 95.14.8 applies to group schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A `T`-point of `ofOver U` determines a morphism `T.unop ⟶ U`. -/
def ofOverPoint {S : Scheme.{u}} {U : Over S} {T : (Over S)ᵒᵖ}
    (p : (ofOver U).functorOfPoints.obj T) : T.unop ⟶ U :=
  (yonedaEquiv.symm p).app (op T.unop) (𝟙 _)

/-- The identity `T`-point of `ofOver T`. -/
def ofOverIdPoint {S : Scheme.{u}} (T : Over S) :
    (ofOver T).functorOfPoints.obj (op T) :=
  yonedaEquiv (𝟙 (yoneda.obj T))

/-- The algebraic space associated to a scheme `T` over `S`, as an object of the
slice over `S` viewed as an algebraic space. -/
def ofOverAsOver {S : Scheme.{u}} (T : Over S) : Over (ofOver (Over.mk (𝟙 S))) :=
  Over.mk (toBase (ofOver T))

/-- The underlying algebraic space of `ofOverAsOver T` is `ofOver T`. -/
theorem ofOverAsOver_left {S : Scheme.{u}} (T : Over S) :
    (ofOverAsOver T).left = ofOver T := sorry

/-- First projection of the slice tensor product of `ofOver X` and `ofOver Y`. -/
def ofOverAsOverFst {S : Scheme.{u}} (X Y : Over S) :
    (ofOverAsOver X ⊗ ofOverAsOver Y).left ⟶ ofOver X :=
  (fst (ofOverAsOver X) (ofOverAsOver Y)).left

/-- Second projection of the slice tensor product of `ofOver X` and `ofOver Y`. -/
def ofOverAsOverSnd {S : Scheme.{u}} (X Y : Over S) :
    (ofOverAsOver X ⊗ ofOverAsOver Y).left ⟶ ofOver Y :=
  (snd (ofOverAsOver X) (ofOverAsOver Y)).left

/-- Comparison from the algebraic-space fibre product of `ofOver X` and `ofOver Y`
over `S` to `ofOver` of the scheme-level tensor product. -/
def ofOverTensor {S : Scheme.{u}} (X Y : Over S) :
    (ofOverAsOver X ⊗ ofOverAsOver Y).left ⟶ ofOver (X ⊗ Y) where
  app T := ↾fun p ↦
    (ofOverMap
      (lift (ofOverPoint ((ofOverAsOverFst X Y).app T p))
        (ofOverPoint ((ofOverAsOverSnd X Y).app T p)))).app T
      (ofOverIdPoint T.unop)
  naturality := sorry

/-- The component of `ofOverTensor` at a test scheme is `ofOverMap` of the Cartesian
lift of the two projections. -/
theorem ofOverTensor_app {S : Scheme.{u}} (X Y : Over S) (T : (Over S)ᵒᵖ)
    (p : (ofOverAsOver X ⊗ ofOverAsOver Y).left.functorOfPoints.obj T) :
    (ofOverTensor X Y).app T p =
      (ofOverMap
        (lift (ofOverPoint ((ofOverAsOverFst X Y).app T p))
          (ofOverPoint ((ofOverAsOverSnd X Y).app T p)))).app T
        (ofOverIdPoint T.unop) := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}}

/-- The group algebraic space over `S` associated to a group scheme `G` over `S`.
The underlying object is `ofOver` of `G.X`, and the structure maps are `ofOverMap`
of the scheme-level group operations. -/
def toGroupAlgebraicSpace (G : GroupScheme S) :
    GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) where
  X := AlgebraicSpace.ofOverAsOver G.X
  grp :=
    { one := Over.homMk (AlgebraicSpace.ofOverMap η[G.X]) sorry
      mul := Over.homMk
        (AlgebraicSpace.ofOverTensor G.X G.X ≫ AlgebraicSpace.ofOverMap μ[G.X]) sorry
      inv := Over.homMk (AlgebraicSpace.ofOverMap ι[G.X]) sorry
      one_mul := sorry
      mul_one := sorry
      mul_assoc := sorry
      left_inv := sorry
      right_inv := sorry }

/-- The underlying slice object of `toGroupAlgebraicSpace G` is `ofOver` of `G.X`
over `S` as an algebraic space. -/
theorem toGroupAlgebraicSpace_X (G : GroupScheme S) :
    (toGroupAlgebraicSpace G).X = AlgebraicSpace.ofOverAsOver G.X := sorry

/-- The underlying algebraic space of `toGroupAlgebraicSpace G` is `ofOver G.X`. -/
theorem toGroupAlgebraicSpace_left (G : GroupScheme S) :
    (toGroupAlgebraicSpace G).X.left = AlgebraicSpace.ofOver G.X := sorry

end AlgebraicGeometry.GroupScheme
