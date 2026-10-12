/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Normal.RationalSingularity
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RationalSingularity

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 54.11.4 (1): the maximal-ideal completion of a rational surface singularity is
again a rational surface singularity, provided that the completion is normal. -/
@[stacks 0BG7] #check
(IsRationalSingularity.instAdicCompletion :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)],
    IsRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal A) A))

/- Lemma 54.11.4 (2): at every closed point of the blowup of a rational surface
singularity in its maximal ideal, the maximal-ideal completion of the stalk is normal. -/
@[stacks 0BG7] #check
(AlgebraicGeometry.IsBlowup.isNormalRing_stalkCompletion :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (x : X) (h_closed : x ∈ closedPoints X),
    IsNormalRing
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)))
