/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_SmallHypercover
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {D : Type u} [Category.{u} D] {C : Type v} [Category.{u} C]
  (F : D ⥤ C) (J : GrothendieckTopology C) [F.Full] [F.Faithful] [F.IsCoverDense J]

include F in
/-- The actual sheaf extension from a small full basis is certified by explicit hypercovers. -/
theorem smallDenseSheafification : HasSheafify J AddCommGrpCat.{u} := by
  let J₀ := F.inducedTopology J
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : F.IsDenseSubsite J₀ J := inferInstance
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := smallOneHypercoverDense F J₀ J
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (F.sheafPushforwardContinuous AddCommGrpCat.{u} J₀ J).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense F J₀ J AddCommGrpCat.{u}
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J₀ J F

include F in
/-- Local bijectivity is transported across the same proved dense-basis equivalence. -/
theorem smallDenseWEquals : J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let J₀ := F.inducedTopology J
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : F.IsDenseSubsite J₀ J := inferInstance
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := smallOneHypercoverDense F J₀ J
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (F.sheafPushforwardContinuous AddCommGrpCat.{u} J₀ J).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense F J₀ J AddCommGrpCat.{u}
  exact GrothendieckTopology.WEqualsLocallyBijective.transport J J₀ F
    (Functor.IsDenseSubsite.coverPreserving J₀ J F)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
