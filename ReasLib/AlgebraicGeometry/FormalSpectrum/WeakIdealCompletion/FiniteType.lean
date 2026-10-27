/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.AlgebraicGeometry.FormalSpectrum.StageFactorization
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdealCompletion.Stages
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Finite type morphisms from weak-ideal completions
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- If `A → A'` is of finite type, then so is each stage map `A ⧸ I → A' ⧸ I A'`. -/
instance finiteType_quotientStage [Algebra.FiniteType A A']
    (I : WeakIdealOfDefinition A) :
    Algebra.FiniteType (A ⧸ I.ideal) (A' ⧸ I.ideal.map (algebraMap A A')) := sorry

/-- If `A → A'` is of finite type, then
`Spf((A')^∧) ⟶ Spf(A)` is of finite type. -/
instance instFiniteType_spfMap_weakIdealCompletion [Algebra.FiniteType A A'] :
    FiniteType (spfMap_weakIdealCompletion hA A').hom := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
