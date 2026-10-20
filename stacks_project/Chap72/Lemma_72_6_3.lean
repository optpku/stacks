/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.HenselianLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Pullback
import StacksCheckRecall

/-!
# Henselian local rings at generic points of prime divisors

On a locally Noetherian integral algebraic space, the henselian local ring at the
generic point of a prime divisor is a reduced 1-dimensional Noetherian local ring,
and the function field embeds canonically into its total ring of fractions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [h_locallyNoetherian : IsLocallyNoetherian X] [h_integral : IsIntegral X]

include h_locallyNoetherian h_integral

/-- The source-facing compatibility name for the canonical henselian comparison at a
prime-divisor generic point. -/
def functionFieldToHenselianFraction (Z : PrimeDivisor X) :
    RationalFunction X →+* FractionRing (henselianLocalRing X Z.genericPoint) :=
  rationalFunctionToHenselianFraction Z.genericPoint

/- Lemma 72.6.3 -/
@[stacks 0ENK] #check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing_genericPoint_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X] (Z : PrimeDivisor X),
      _root_.IsReduced (henselianLocalRing X Z.genericPoint) ∧
        IsNoetherianRing (henselianLocalRing X Z.genericPoint) ∧
        IsLocalRing (henselianLocalRing X Z.genericPoint) ∧
        ringKrullDim (henselianLocalRing X Z.genericPoint) = 1 ∧
        Function.Injective (rationalFunctionToHenselianFraction Z.genericPoint))

#check
  (AlgebraicGeometry.AlgebraicSpace.rationalFunctionToHenselianFraction_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X] (x : Points X)
      (U : EtaleNeighborhood.Elementary X x) [IsAffine U.obj.scheme]
      (f : RationalFunction X),
      rationalFunctionToHenselianFraction x f =
        rationalFunctionHenselianChartMap x U f)

#check
  (AlgebraicGeometry.AlgebraicSpace.sectionsFractionsToRationalFunction_algebraMap :
    ∀ {S : Scheme.{u}} (T : Over S)
      [AlgebraicGeometry.IsIntegral T.left]
      (s : Γ(T.left, ⊤)),
      sectionsFractionsToRationalFunction T (algebraMap _ _ s) =
        sectionsToRationalFunction T s)

end AlgebraicGeometry.AlgebraicSpace
