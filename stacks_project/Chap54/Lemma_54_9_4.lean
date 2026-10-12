/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RationalSingularity

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 54.9.4: in the situation of a rational surface singularity, the blowup of
`Spec A` in the maximal ideal of `A` is normal. -/
@[stacks 0B4Z] #check
(AlgebraicGeometry.IsBlowup.isNormal_of_isRationalSingularity :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
    X.isNormal)
