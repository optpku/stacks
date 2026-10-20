/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RationalSingularity.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 54.9.2 (1): on a normal modification of a rational surface singularity,
the cohomology of a quasi-coherent module vanishes in every degree greater than one. -/
@[stacks 0B4X] #check
(IsRationalSingularity.cohomology_isZero_of_one_lt :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (hX : X.isNormal) (F : X.Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : 1 < p),
    IsZero (Scheme.Modules.cohomology F p))

/- Lemma 54.9.2 (2): a globally generated quasi-coherent module on a normal
modification of a rational surface singularity has vanishing first cohomology. -/
@[stacks 0B4X] #check
(IsRationalSingularity.firstCohomology_isZero_of_isGloballyGenerated :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (hX : X.isNormal) (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsGloballyGenerated F],
    IsZero (Scheme.Modules.cohomology F 1))
