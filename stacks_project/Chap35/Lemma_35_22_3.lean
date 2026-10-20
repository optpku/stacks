/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.TargetLocus

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 35.22.3 (1): for a non-Zariski standard topology, the target locus is
the greatest target open over which the restricted morphism has the property. -/
@[stacks 06QP] #check
  (CategoryTheory.MorphismProperty.targetLocus_isGreatest_nonZariski :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
        (τ : StandardTopology) (_ : τ ≠ .zariski)
        [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y),
      IsGreatest {U : Y.Opens | P (f ∣_ U)} (P.targetLocus f))

/- Lemma 35.22.3 (2): if a matching standard base change has the property, the
range of the base-change morphism lies in the target locus. -/
@[stacks 06QP] #check
  (CategoryTheory.MorphismProperty.range_subset_targetLocus_nonZariski :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y Y' : Scheme.{u}}
        (τ : StandardTopology) (_ : τ ≠ .zariski)
        [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y) (g : Y' ⟶ Y),
      τ.precoverage.morphismProperty g → P (pullback.snd f g) →
        Set.range g ⊆ P.targetLocus f)

/- Lemma 35.22.3 (3): target loci commute with matching non-Zariski standard
base changes. -/
@[stacks 06QP] #check
  (CategoryTheory.MorphismProperty.targetLocus_preimage_nonZariski :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y Y' : Scheme.{u}}
        (τ : StandardTopology) (_ : τ ≠ .zariski)
        [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y) (g : Y' ⟶ Y),
      τ.precoverage.morphismProperty g →
        g ⁻¹ᵁ P.targetLocus f = P.targetLocus (pullback.snd f g))

/- Lemma 35.22.3 (4): target loci commute with each member of a matching
non-Zariski standard covering family. -/
@[stacks 06QP] #check
  (CategoryTheory.MorphismProperty.targetLocus_preimage_cover_nonZariski :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
        (τ : StandardTopology) (_ : τ ≠ .zariski)
        [P.IsLocalAtTarget τ.precoverage] (f : X ⟶ Y)
        (𝒰 : Scheme.Cover τ.precoverage Y) (i : 𝒰.I₀),
      𝒰.f i ⁻¹ᵁ P.targetLocus f =
        P.targetLocus (pullback.snd f (𝒰.f i)))
