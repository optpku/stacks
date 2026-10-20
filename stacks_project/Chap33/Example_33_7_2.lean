/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.RatSqrtNegOne
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

#check (AlgebraicGeometry.ratSqrtNegOneOverRatVariety :
  AlgebraicGeometry.Variety AlgebraicGeometry.ratSqrtNegOneOverRat)

#check (AlgebraicGeometry.RatSqrtNegOne.complexBaseChangeIsoSpec :
  AlgebraicGeometry.RatSqrtNegOne.complexBaseChange ≅
    AlgebraicGeometry.RatSqrtNegOne.complexTensorSpec)

#check (AlgebraicGeometry.RatSqrtNegOne.complexTensorEquivProd :
  AlgebraicGeometry.RatSqrtNegOne.complexTensor ≃+* (ℂ × ℂ))

#check (AlgebraicGeometry.RatSqrtNegOne.complexBaseChangeIsoCoprod :
  AlgebraicGeometry.RatSqrtNegOne.complexBaseChange ≅
    AlgebraicGeometry.Spec (CommRingCat.of ℂ) ⨿
      AlgebraicGeometry.Spec (CommRingCat.of ℂ))

#check (AlgebraicGeometry.RatSqrtNegOne.complexBaseChangeNotConnected :
  ¬ ConnectedSpace AlgebraicGeometry.RatSqrtNegOne.complexBaseChange)

/- Example 33.7.2: the variety `Spec(ℚ(i))` over `Spec(ℚ)` becomes the disjoint union of two
copies of `Spec(ℂ)` after base change to `ℂ`, so it is not geometrically connected. -/
@[stacks 020E] #check (AlgebraicGeometry.RatSqrtNegOne.notGeometricallyConnected :
  ¬ AlgebraicGeometry.GeometricallyConnected AlgebraicGeometry.ratSqrtNegOneToSpecRat)
