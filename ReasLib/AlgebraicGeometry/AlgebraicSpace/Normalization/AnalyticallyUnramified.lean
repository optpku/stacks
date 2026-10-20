/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified

/-!
# Finiteness of absolute normalization over an analytically unramified local ring
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space locally of finite type over an analytically unramified
Noetherian local ring has finite absolute normalization if its structural morphism
is étale at every point of codimension zero. -/
@[stacks 0BHR]
theorem isFinite_normalizationTo_of_analyticallyUnramified_of_codimZeroEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAnalyticallyUnramified A] (X : AlgebraicSpace (Spec (.of A)))
    [LocallyOfFiniteType (SchemeRealization.toBase X)]
    (h_etale : ∀ x : Points X, x ∈ codimZeroPoints X →
      EtaleAt (SchemeRealization.toBase X) x) :
    IsFinite X.normalizationTo :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
