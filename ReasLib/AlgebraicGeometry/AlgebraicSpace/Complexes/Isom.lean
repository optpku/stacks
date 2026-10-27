/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom

/-!
# Isomorphism presheaves of relatively perfect complexes

Fibrewise isomorphism presheaves of admissible complexes are transported to
schemes over each test scheme and compared with algebraic-space functors of
points after a universe lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The projection from relatively perfect fibre complexes with vanishing
negative self-Ext to test schemes is fibred. -/
instance instIsFibered (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    Functor.IsFibered (p f) := sorry

/-- The isomorphism presheaf of two fibre objects of `p f` over `T`, reindexed
along the inverse iterated-slice equivalence to schemes over `T.left`.
Its values lie in `Type (u + 1)`. -/
def isomOverLeft {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) : (Over T.left)ᵒᵖ ⥤ Type (u + 1) :=
  T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y

/-- The transported isomorphism presheaf is the canonical fibrewise Isom
presheaf precomposed with the opposite of the iterated-slice inverse. -/
theorem isomOverLeft_eq {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) :
    isomOverLeft x y =
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y := sorry

/-- The transported isomorphism presheaf of a pair of fibre objects is
represented by an algebraic space over the test scheme after universe lift. -/
def isAlgebraicSpaceAt {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) : Prop :=
  ∃ F : AlgebraicSpace T.left,
    Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

/-- Representability at a fibre pair means that an algebraic space over
`T.left` has universe-lifted functor of points isomorphic to its Isom presheaf. -/
theorem isAlgebraicSpaceAt_iff {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {T : Over S} (x y : (p f).Fiber T) :
    isAlgebraicSpaceAt x y ↔
      ∃ F : AlgebraicSpace T.left,
        Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) := sorry

/-- Every pair of fibre objects of `p f` has an algebraic-space isomorphism
presheaf over its test scheme, at Hom-universe `u + 1`. -/
def isAlgebraicSpace (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] : Prop :=
  ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y

/-- The global algebraic-space Isom condition holds exactly when pointwise
representability holds at every test scheme and every pair of fibre objects. -/
theorem isAlgebraicSpace_iff (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    isAlgebraicSpace f ↔
      ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y := sorry

/-- For a proper, flat, finitely presented morphism of algebraic spaces, every
fibrewise isomorphism presheaf of relatively perfect complexes with vanishing
negative self-Ext is represented by an algebraic space over its test scheme. -/
theorem isom_isAlgebraicSpace (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    isAlgebraicSpace f := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
