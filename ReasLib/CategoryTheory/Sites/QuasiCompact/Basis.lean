/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.FilteredColimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-compact bases of sites

The three hypotheses used for a quasi-compact basis are deliberately kept independent.  Results
that only need enough basis objects, or only need their quasi-compactness, therefore do not inherit
the stronger pairwise-overlap assumption.
-/

@[expose] public section

open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace CategoryTheory.Coverage

variable {C : Type u} [Category.{v} C]

/-- A chosen covering family has quasi-compact pairwise overlaps when every pullback of two
members is quasi-compact for the same coverage. -/
@[stacks 0937 "(3), pairwise-overlap predicate"]
def pairwiseOverlaps (K : Coverage C)
    {U : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} U)
    [𝒰.toPresieve.HasPairwisePullbacks] : Prop :=
  ∀ i j : 𝒰.index,
    K.QuasiCompactObject (Limits.pullback (𝒰.obj i).hom (𝒰.obj j).hom)

namespace Basis

variable (K : Coverage C) (B : Set C)

/-- Situation 18.30.5 (0937) (2): every object belonging to the selected basis is
quasi-compact for the chosen coverage. -/
@[stacks 0937 "(2)"]
def IsQuasiCompact : Prop :=
  ∀ ⦃U : C⦄, U ∈ B → K.QuasiCompactObject U

/-- Situation 18.30.5 (0937) (3): a chosen basis cover of a basis object has pairwise
pullbacks, and all those overlaps are quasi-compact for the chosen coverage. -/
@[stacks 0937 "(3)"]
def HasQuasiCompactOverlaps : Prop :=
  ∀ ⦃U : C⦄, U ∈ B →
    ∀ (𝒰 : SemiRepresentableFamily.Over.{max u v} U), 𝒰.toPresieve ∈ K U →
      (∀ i, (𝒰.obj i).left ∈ B) →
        ∃ hpair : 𝒰.toPresieve.HasPairwisePullbacks,
          @Coverage.pairwiseOverlaps C _ K U 𝒰 hpair

end Basis

end CategoryTheory.Coverage

namespace CategoryTheory.GrothendieckTopology.Basis

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (B : Set C)

/-- Situation 18.30.5 (0937) (2), sieve-saturated specialization: every basis object is
quasi-compact for the ambient Grothendieck topology. -/
@[stacks 0937 "(2), sieve-saturated specialization"]
def IsQuasiCompact : Prop :=
  ∀ ⦃U : C⦄, U ∈ B → J.QuasiCompactObject U

/-- Situation 18.30.5 (0937) (3), sieve-saturated specialization: a basis cover has pairwise
pullbacks whose objects are quasi-compact for the ambient Grothendieck topology. -/
@[stacks 0937 "(3), sieve-saturated specialization"]
def HasQuasiCompactOverlaps : Prop :=
  ∀ ⦃U : C⦄, U ∈ B →
    ∀ (𝒰 : SemiRepresentableFamily.Over.{max u v} U), 𝒰.toSieve ∈ J U →
      (∀ i, (𝒰.obj i).left ∈ B) →
        ∃ hpair : 𝒰.toPresieve.HasPairwisePullbacks,
          @GrothendieckTopology.pairwiseOverlaps C _ J U 𝒰 hpair

end CategoryTheory.GrothendieckTopology.Basis
