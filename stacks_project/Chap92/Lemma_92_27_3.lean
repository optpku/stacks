/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.NaiveDifferentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.DerivedLowerShriek
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 92.27.3 -/
@[stacks 08VM] #check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.lowerShriek_omega :
    ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
      IsIsomorphic (AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangent
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X))
        ((AlgebraicGeometry.AlgebraicSpace.Cotangent.lowerShriek Λ X).obj
          (AlgebraicGeometry.AlgebraicSpace.Cotangent.singleOmegaTensorInverseImage Λ X)))

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.derivedInverseImage_omega :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    IsIsomorphic
      ((AlgebraicGeometry.AlgebraicSpace.Cotangent.derivedInverseImage Λ X).obj
        (AlgebraicGeometry.AlgebraicSpace.Cotangent.singleOmega Λ X))
      (AlgebraicGeometry.AlgebraicSpace.Cotangent.singleOmegaTensor Λ X))

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.lowerShriek_derivedInverseImage :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    IsIsomorphic
      ((AlgebraicGeometry.AlgebraicSpace.Cotangent.lowerShriek Λ X).obj
        ((AlgebraicGeometry.AlgebraicSpace.Cotangent.transportDerived Λ X).obj
          ((AlgebraicGeometry.AlgebraicSpace.Cotangent.derivedInverseImage Λ X).obj
            (AlgebraicGeometry.AlgebraicSpace.Cotangent.singleOmega Λ X))))
      ((AlgebraicGeometry.AlgebraicSpace.Cotangent.lowerShriek Λ X).obj
        (AlgebraicGeometry.AlgebraicSpace.Cotangent.singleOmegaTensorInverseImage Λ X)))
