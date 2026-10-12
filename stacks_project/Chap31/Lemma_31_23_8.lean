/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.Pullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.23.8: a morphism of locally ringed spaces that preserves the canonical meromorphic
denominators induces pullback on meromorphic sections of every module sheaf. -/
@[stacks 02OY] #check
  (AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackMeromorphicSections :
    ∀ {X Y : AlgebraicGeometry.LocallyRingedSpace.{u}} (f : X ⟶ Y)
      (_ : AlgebraicGeometry.LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
        f)
      (ℱ : Y.Modules),
      Y.meromorphicSections ℱ →
        X.meromorphicSections
          ((AlgebraicGeometry.RingedSpace.Hom.pullback f.toShHom).obj ℱ))

/- For an invertible module, the canonical pullback carries regular meromorphic sections to
regular meromorphic sections. -/
#check
  (AlgebraicGeometry.LocallyRingedSpace.IsRegularMeromorphicSection.pullback :
    ∀ {X Y : AlgebraicGeometry.LocallyRingedSpace.{u}} (f : X ⟶ Y)
      (hf : AlgebraicGeometry.LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
        f)
      (ℒ : Y.Modules) [CategoryTheory.MonoidalCategory.isInvertibleObject ℒ]
      (s : Y.meromorphicSections ℒ),
      Y.IsRegularMeromorphicSection ℒ s →
        X.IsRegularMeromorphicSection
          ((AlgebraicGeometry.RingedSpace.Hom.pullback f.toShHom).obj ℒ)
          (AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackMeromorphicSections
            f hf ℒ s))
