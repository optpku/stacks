/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.ProperSupport

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Over an adically complete Noetherian affine base, completion on a finite-type
separated algebraic space is an equivalence from coherent modules with proper
support to coherent formal modules whose first stage has proper support. -/
instance instIsEquivalence_coherentProperSupportCompletionFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)] :
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
