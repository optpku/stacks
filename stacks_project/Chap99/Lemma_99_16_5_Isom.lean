/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Isom

/-!
# Isomorphism presheaves of the category of complexes

The fibrewise Isom API is owned by the shared library and re-exported here for
consumers of the category of complexes in Situation 99.16.3.
-/

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor
open AlgebraicGeometry.AlgebraicSpace.Complexes

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable {f : X ⟶ B} [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f]
  [AlgebraicSpace.FinitePresentation f]

#check (isomOverLeft :
  ∀ {T : Over S} (x y : (p f).Fiber T), (Over T.left)ᵒᵖ ⥤ Type (u + 1))

#check (isomOverLeft_eq :
  ∀ {T : Over S} (x y : (p f).Fiber T),
    isomOverLeft x y =
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y)

#check (isAlgebraicSpaceAt : ∀ {T : Over S} (x y : (p f).Fiber T), Prop)

#check (isAlgebraicSpaceAt_iff :
  ∀ {T : Over S} (x y : (p f).Fiber T),
    isAlgebraicSpaceAt x y ↔
      ∃ F : AlgebraicSpace T.left,
        Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}))

#check (isAlgebraicSpace :
  ∀ (f : X ⟶ B) [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f]
    [AlgebraicSpace.FinitePresentation f], Prop)

#check (isAlgebraicSpace_iff :
  ∀ (f : X ⟶ B) [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f]
    [AlgebraicSpace.FinitePresentation f],
    isAlgebraicSpace f ↔
      ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y)
