/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom

/-!
# Isomorphism presheaves of finitely presented flat modules with proper support

Fibrewise isomorphism presheaves of the projection to test schemes are
transported along the iterated slice equivalence and compared with functors
of points of algebraic spaces after a universe lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The projection from finitely presented flat modules with proper support
on scheme-valued fibres to test schemes is fibred. -/
instance instIsFibered (f : X ⟶ B) [FinitePresentation f] :
    Functor.IsFibered (p f) := sorry

/-- The isomorphism presheaf of two fibre objects of `p f` over a scheme `T`
over `S`, reindexed along `T.iteratedSliceEquiv` to a presheaf on schemes over
`T.left`. Hom-types of `Obj f` live in `Type (u + 1)`. -/
def isomOverLeft {f : X ⟶ B} [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) : (Over T.left)ᵒᵖ ⥤ Type (u + 1) :=
  T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y

/-- `isomOverLeft x y` is precomposition of `Functor.isomorphismPresheaf (p f) x y`
with the opposite of the iterated-slice inverse. -/
theorem isomOverLeft_eq {f : X ⟶ B} [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) :
    isomOverLeft x y =
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y := sorry

/-- The transported isomorphism presheaf at a pair of fibre objects is an
algebraic space over `T`, after universe lift of the functor of points. -/
def isAlgebraicSpaceAt {f : X ⟶ B} [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) : Prop :=
  ∃ F : AlgebraicSpace T.left,
    Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

/-- Being an algebraic space over `T` means some algebraic space over `T.left`
has functor of points isomorphic to `isomOverLeft x y` after universe lift. -/
theorem isAlgebraicSpaceAt_iff {f : X ⟶ B} [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) :
    isAlgebraicSpaceAt x y ↔
      ∃ F : AlgebraicSpace T.left,
        Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) := sorry

/-- Every pair of fibre objects of `p f` has an algebraic-space isomorphism
presheaf over its base, at Hom-universe `u + 1`. -/
def isAlgebraicSpace (f : X ⟶ B) [FinitePresentation f] : Prop :=
  ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y

/-- The global algebraic-space Isom condition holds exactly when
`isAlgebraicSpaceAt` holds at every fibre pair. -/
theorem isAlgebraicSpace_iff (f : X ⟶ B) [FinitePresentation f] :
    isAlgebraicSpace f ↔
      ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y := sorry

/-- For a finite-presentation morphism of algebraic spaces, every fibrewise
isomorphism presheaf of finitely presented flat modules with proper support
is represented by an algebraic space over its test scheme. -/
theorem isom_isAlgebraicSpace (f : X ⟶ B) [FinitePresentation f] :
    isAlgebraicSpace f := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
