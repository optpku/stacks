/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.RationalSingularity.SpecialFiberIdeal
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The blowup of the spectrum of a rational surface singularity in its maximal ideal
is normal when its structure morphism is a modification. -/
theorem isNormal_of_isRationalSingularity
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    X.isNormal := sorry

/-- At every closed point of the maximal-ideal blowup of a rational surface singularity
with normal completion, the maximal-ideal completion of the stalk is normal. -/
theorem isNormalRing_stalkCompletion
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (x : X) (h_closed : x ∈ closedPoints X) :
    IsNormalRing
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) := sorry

end AlgebraicGeometry.IsBlowup
