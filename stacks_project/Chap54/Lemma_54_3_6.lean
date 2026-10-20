/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RelativeDifferentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 54.3.6 -/
@[stacks 0B4L] #check
  (AlgebraicGeometry.IsBlowup.relativeDifferentials_isIsomorphic_pushforward_exceptional :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
      ringKrullDim A = 2 → {X : Scheme.{u}} → (f : X ⟶ Spec (.of A)) →
        [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] →
          let I := Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A)
          let E := exceptionalIdeal (IsLocalRing.maximalIdeal A) f
          IsIsomorphic Ω[f.toShHom]
            ((Scheme.Modules.pushforward E.subschemeι).obj
              Ω[(exceptionalProjection I f).toShHom]))

end AlgebraicGeometry.IsBlowup
