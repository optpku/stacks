/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 35.26.3 (1): for any non-Zariski standard topology and any property
local on the source in that topology, `P.sourceLocus f` is the largest source
open on which the restriction of `f` has property `P`. -/
@[stacks 0CEY] #check
  (CategoryTheory.MorphismProperty.sourceLocus_isGreatest_nonZariski :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
        (tau : StandardTopology) (_ : tau ≠ .zariski)
        [P.IsLocalAtSource tau.precoverage] (f : X ⟶ Y),
      IsGreatest {U : X.Opens | P (U.ι ≫ f)} (P.sourceLocus f))

/- Lemma 35.26.3 (2): the largest good source open for an fppf-local property
pulls back along flat, locally finitely presented morphisms. -/
@[stacks 0CEY] #check
  (CategoryTheory.MorphismProperty.sourceLocus_preimage_fppf :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y X' : Scheme.{u}}
        [P.IsLocalAtSource Scheme.fppfPrecoverage]
        (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFinitePresentation g],
      g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f))

/- Lemma 35.26.3 (3): the largest good source open for a syntomic-local
property pulls back along syntomic morphisms. -/
@[stacks 0CEY] #check
  (CategoryTheory.MorphismProperty.sourceLocus_preimage_syntomic :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y X' : Scheme.{u}}
        [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage]
        (f : X ⟶ Y) (g : X' ⟶ X) [Syntomic g],
      g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f))

/- Lemma 35.26.3 (4): the largest good source open for a smooth-local property
pulls back along smooth morphisms. -/
@[stacks 0CEY] #check
  (CategoryTheory.MorphismProperty.sourceLocus_preimage_smooth :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y X' : Scheme.{u}}
        [P.IsLocalAtSource Scheme.bigSmoothPrecoverage]
        (f : X ⟶ Y) (g : X' ⟶ X) [Smooth g],
      g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f))

/- Lemma 35.26.3 (5): the largest good source open for an étale-local property
pulls back along étale morphisms. -/
@[stacks 0CEY] #check
  (CategoryTheory.MorphismProperty.sourceLocus_preimage_etale :
    ∀ (P : MorphismProperty Scheme.{u}) {X Y X' : Scheme.{u}}
        [P.IsLocalAtSource Scheme.etalePrecoverage]
        (f : X ⟶ Y) (g : X' ⟶ X) [Etale g],
      g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f))
