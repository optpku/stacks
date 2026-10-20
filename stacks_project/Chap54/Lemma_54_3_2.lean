/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Regular

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsBlowup

/- Lemma 54.3.2 (1): the blowup of the spectrum of a two-dimensional regular local ring at its
maximal ideal is irreducible. -/
@[stacks 0AGR] #check
  (AlgebraicGeometry.IsBlowup.irreducibleSpace_of_maximalIdeal :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] (h_dim : ringKrullDim A = 2)
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      IrreducibleSpace X)

/- Lemma 54.3.2 (2): the blowup of the spectrum of a two-dimensional regular local ring at its
maximal ideal is a regular scheme. -/
@[stacks 0AGR] #check
  (AlgebraicGeometry.IsBlowup.regular_of_maximalIdeal :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] (h_dim : ringKrullDim A = 2)
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
      [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
      Scheme.Regular X)

end AlgebraicGeometry.IsBlowup
