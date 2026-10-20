/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Group and action structures on Isom algebraic spaces

The diagonal Isom space `Isom_X(y, y)` is a group algebraic space over `T` via
identity, composition, and inversion of fibre isomorphisms. Off the diagonal,
`Isom_X(x, y)` carries the postcomposition action of `Isom_X(y, y)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor Limits
open FiberedCategoryOver.Groupoids
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Isom

/-- Composition of fibre isomorphisms, as a pointwise operation on
`Functor.isomorphismPresheaf`. -/
def isomComp {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    {x y z : X.p.Fiber T} {W : (Over T)ᵒᵖ}
    (φ : (Functor.isomorphismPresheaf X.p x y).obj W)
    (ψ : (Functor.isomorphismPresheaf X.p y z).obj W) :
    (Functor.isomorphismPresheaf X.p x z).obj W :=
  ⟨φ.1 ≫ ψ.1, sorry⟩

/-- Inversion of a fibre isomorphism, as a pointwise operation on
`Functor.isomorphismPresheaf`. -/
def isomInv {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    {x y : X.p.Fiber T} {W : (Over T)ᵒᵖ}
    (φ : (Functor.isomorphismPresheaf X.p x y).obj W) :
    (Functor.isomorphismPresheaf X.p y x).obj W :=
  have : IsIso φ.1 := φ.property
  ⟨_root_.CategoryTheory.inv φ.1, sorry⟩

/-- Composition of fibre isomorphisms on `isomOverLeft` sections. -/
def isomOverLeftComp {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    {x y z : X.p.Fiber T} {W : (Over T.left)ᵒᵖ}
    (φ : (isomOverLeft x y).obj W) (ψ : (isomOverLeft y z).obj W) :
    (isomOverLeft x z).obj W :=
  isomComp φ ψ

/-- Inversion of fibre isomorphisms on `isomOverLeft` sections. -/
def isomOverLeftInv {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    {x y : X.p.Fiber T} {W : (Over T.left)ᵒᵖ}
    (φ : (isomOverLeft x y).obj W) : (isomOverLeft y x).obj W :=
  isomInv φ

/-- Identity isomorphism of `y` as a section of `Isom_X(y, y)` over `T`. -/
def identitySliceSection {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (y : X.p.Fiber T) :
    (Functor.isomorphismPresheaf X.p y y).obj (op (Over.mk (𝟙 T))) :=
  ⟨(Functor.fiberPseudofunctor X.p).presheafHomObjHomEquiv (𝟙 y), sorry⟩

/-- Identity isomorphism of `y`, transported to a section of `isomOverLeft y y`
over `T`. -/
def identitySection {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (y : X.p.Fiber T) :
    (isomOverLeft y y).obj (op (Over.mk (𝟙 T.left))) :=
  (Functor.isomorphismPresheaf X.p y y).map
    (T.iteratedSliceEquiv.unitIso.app (Over.mk (𝟙 T))).inv.op
    (identitySliceSection y)

/-- The identity section of `Isom_X(y, y)` as a morphism from `T`. -/
def oneLeft {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    selfSpace T ⟶ isomSpace y y :=
  yonedaEquiv.symm (identitySection y)

/-- The unit morphism of `Isom_X(y, y)` over `T`. -/
def oneHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    𝟙_ (Over (selfSpace T)) ⟶ isomOver y y :=
  Over.homMk (oneLeft y) sorry

/-- The underlying algebraic-space map of `oneHom y` is `oneLeft y`. -/
theorem oneHom_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    (oneHom y).left = oneLeft y :=
  sorry

/-- Multiplication of `Isom_X(y, y)` on the explicit product of functors of
points, by composition of fibre isomorphisms: a pair `(φ, ψ)` is sent
to `ψ ≫ φ`. -/
def mulOnProduct {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    AlgebraicSpace.product (isomSpace y y) (isomSpace y y) ⟶ isomSpace y y where
  app W := ↾fun p ↦
    isomOverLeftComp
      ((AlgebraicSpace.productSnd (isomSpace y y) (isomSpace y y)).app W p)
      ((AlgebraicSpace.productFst (isomSpace y y) (isomSpace y y)).app W p)
  naturality := sorry

/-- The component of `mulOnProduct y` sends a pair `(φ, ψ)` to `ψ ≫ φ`. -/
theorem mulOnProduct_app {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (y : X.p.Fiber T) (W : (Over T.left)ᵒᵖ)
    (p : (AlgebraicSpace.product (isomSpace y y) (isomSpace y y)).functorOfPoints.obj W) :
    (mulOnProduct y).app W p =
      isomOverLeftComp
        ((AlgebraicSpace.productSnd (isomSpace y y) (isomSpace y y)).app W p)
        ((AlgebraicSpace.productFst (isomSpace y y) (isomSpace y y)).app W p) :=
  sorry

/-- The pairing of cartesian projections of `isomOver y y ⊗ isomOver y y` into
the explicit product of functors of points. -/
def tensorToProduct {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    (isomOver y y ⊗ isomOver y y).left ⟶
      AlgebraicSpace.product (isomSpace y y) (isomSpace y y) :=
  AlgebraicSpace.productLift
    (fst (isomOver y y) (isomOver y y)).left
    (snd (isomOver y y) (isomOver y y)).left

/-- The multiplication morphism of `Isom_X(y, y)` over `T`. -/
def mulHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    isomOver y y ⊗ isomOver y y ⟶ isomOver y y :=
  Over.homMk (tensorToProduct y ≫ mulOnProduct y) sorry

/-- The underlying algebraic-space map of `mulHom y` is the composite of
`tensorToProduct y` with composition of isomorphisms. -/
theorem mulHom_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    (mulHom y).left = tensorToProduct y ≫ mulOnProduct y :=
  sorry

/-- Inversion on `Isom_X(y, y)`, by inversion of fibre isomorphisms. -/
def invLeft {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    isomSpace y y ⟶ isomSpace y y where
  app W := ↾fun φ ↦ isomOverLeftInv φ
  naturality := sorry

/-- The inverse morphism of `Isom_X(y, y)` over `T`. -/
def invHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    isomOver y y ⟶ isomOver y y :=
  Over.homMk (invLeft y) sorry

/-- The underlying algebraic-space map of `invHom y` is `invLeft y`. -/
theorem invHom_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    (invHom y).left = invLeft y :=
  sorry

/-- The canonical group-object structure on `Isom_X(y, y)` over `T`. -/
instance instGrpObj_isomOver {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (y : X.p.Fiber T) :
    GrpObj (isomOver y y) where
  one := oneHom y
  mul := mulHom y
  inv := invHom y
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The group algebraic space `Isom_X(y, y)` over `T`. -/
def automorphismGroup {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T) :
    GroupAlgebraicSpace (selfSpace T) :=
  ⟨isomOver y y⟩

/-- Postcomposition of an isomorphism `x ⟶ y` by an automorphism of `y`, on
the explicit product of functors of points. -/
def smulOnProduct {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    AlgebraicSpace.product (isomSpace y y) (isomSpace x y) ⟶ isomSpace x y where
  app W := ↾fun p ↦
    isomOverLeftComp
      ((AlgebraicSpace.productSnd (isomSpace y y) (isomSpace x y)).app W p)
      ((AlgebraicSpace.productFst (isomSpace y y) (isomSpace x y)).app W p)
  naturality := sorry

/-- The component of `smulOnProduct x y` is postcomposition of the `Isom_X(x, y)`
section by the `Isom_X(y, y)` section. -/
theorem smulOnProduct_app {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) (W : (Over T.left)ᵒᵖ)
    (p : (AlgebraicSpace.product (isomSpace y y) (isomSpace x y)).functorOfPoints.obj W) :
    (smulOnProduct x y).app W p =
      isomOverLeftComp
        ((AlgebraicSpace.productSnd (isomSpace y y) (isomSpace x y)).app W p)
        ((AlgebraicSpace.productFst (isomSpace y y) (isomSpace x y)).app W p) :=
  sorry

/-- The pairing of cartesian projections of `isomOver y y ⊗ isomOver x y` into
the explicit product of functors of points. -/
def smulTensorToProduct {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (isomOver y y ⊗ isomOver x y).left ⟶
      AlgebraicSpace.product (isomSpace y y) (isomSpace x y) :=
  AlgebraicSpace.productLift
    (fst (isomOver y y) (isomOver x y)).left
    (snd (isomOver y y) (isomOver x y)).left

/-- The action morphism of `Isom_X(y, y)` on `Isom_X(x, y)` over `T`. -/
def smulHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    isomOver y y ⊗ isomOver x y ⟶ isomOver x y :=
  Over.homMk (smulTensorToProduct x y ≫ smulOnProduct x y) sorry

/-- The underlying algebraic-space map of `smulHom x y` is the composite of
`smulTensorToProduct x y` with postcomposition of isomorphisms. -/
theorem smulHom_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (smulHom x y).left = smulTensorToProduct x y ≫ smulOnProduct x y :=
  sorry

/-- The canonical module-object structure of `Isom_X(y, y)` on `Isom_X(x, y)`. -/
instance instModObj_isomOver {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    ModObj (isomOver y y) (isomOver x y) where
  smul := smulHom x y
  one_smul := sorry
  mul_smul := sorry

/-- The module structure of `automorphismGroup y` on `isomOver x y`. -/
instance instModObj_automorphismGroup {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    ModObj (automorphismGroup y).X (isomOver x y) :=
  instModObj_isomOver x y

/-- The action of `Isom_X(y, y)` on `Isom_X(x, y)` over `T`. -/
def action {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    GroupAlgebraicSpace.Action (automorphismGroup y) :=
  GroupAlgebraicSpace.Action.of (automorphismGroup y) (isomOver x y)

/-- The underlying object of `action x y` is `isomOver x y`. -/
theorem action_X {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (action x y).X = isomOver x y :=
  sorry

/-- The carrier of the automorphism group algebraic space of `y` is its Isom space over `T`. -/
@[stacks 04YP]
theorem automorphismGroup_X {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (y : X.p.Fiber T) :
    (automorphismGroup y).X = isomOver y y :=
  sorry

/-- The postcomposition action on `Isom_X(x, y)` is a pseudo-torsor under the automorphism
group algebraic space of `y` over `T`. -/
@[stacks 04YP, instance]
instance instIsPseudoTorsor_action {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    Mod.IsPseudoTorsor (action x y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Isom
