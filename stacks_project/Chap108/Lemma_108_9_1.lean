/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Over
public import stacks_project.Chap108.Lemma_108_9_1_Map

/-!
# Lemma 108.9.1

The tautological morphism from the Picard stack to the Picard functor is a
gerbe morphism of stacks in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.9.1: the morphism `toPicardFunctor f` turns the Picard stack into
a gerbe over the Picard functor, in the sense of
`CartesianBasedFunctor.IsGerbeMorphism`. -/
@[stacks 0DME]
theorem toPicardFunctor_isGerbeMorphism (f : X ⟶ B) :
    CartesianBasedFunctor.IsGerbeMorphism (Scheme.fppfTopology.over S)
      (toPicardFunctor f) :=
  sorry

/-- The morphism `toPicardFunctor f` is a gerbe morphism if and only if it is
locally essentially surjective on fibre objects and locally lifts fibre
morphisms, the two local conditions of Stacks Lemma 8.11.3. -/
theorem toPicardFunctor_isGerbeMorphism_iff (f : X ⟶ B) :
    CartesianBasedFunctor.IsGerbeMorphism (Scheme.fppfTopology.over S)
        (toPicardFunctor f) ↔
      CartesianBasedFunctor.LocallyEssentiallySurjective
          (Scheme.fppfTopology.over S) (toPicardFunctor f) ∧
      CartesianBasedFunctor.LocallyLifts (Scheme.fppfTopology.over S)
        (toPicardFunctor f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
