/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj.Topology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 28.26.10: if positive-degree homogeneous nonvanishing opens of an invertible module
cover a quasi-compact scheme, then the resulting canonical morphism to the projective spectrum
of its section ring is quasi-compact and has dense image. -/
@[stacks 01Q0]
#check (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.quasiCompact_and_isDominant :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
    {L : X.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]
    {f : X ⟶ AlgebraicGeometry.Proj
      (AlgebraicGeometry.RingedSpace.GradedSections.grading L)},
    AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap L f →
      AlgebraicGeometry.QuasiCompact f ∧ AlgebraicGeometry.IsDominant f)

/- The positive homogeneous cover supplies the canonical section-ring projective morphism. -/
#check (AlgebraicGeometry.Scheme.Modules.exists_sectionRingProj :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.Scheme.Modules.Invertible L],
    AlgebraicGeometry.Scheme.Modules.IsSectionRingCover L →
      ∃ f : X ⟶ AlgebraicGeometry.Proj
        (AlgebraicGeometry.RingedSpace.GradedSections.grading L),
        AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap L f)
