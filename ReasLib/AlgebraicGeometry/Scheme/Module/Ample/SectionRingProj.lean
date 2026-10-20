/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj

/-!
# Ample invertible modules and section-ring projective spectra

An ample invertible module satisfies the positive-degree section-cover condition and therefore
determines a morphism to the projective spectrum of its tensor-power section ring.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The positive-degree nonvanishing opens of an ample invertible module cover the scheme. -/
theorem IsAmple.isSectionRingCover {L : X.Modules} [Invertible L] (hL : IsAmple L) :
    IsSectionRingCover L := sorry

/-- An ample invertible module determines a morphism to the projective spectrum of its section
ring with the canonical basic-open and twist-comparison properties. -/
theorem IsAmple.exists_sectionRingProj {L : X.Modules} [Invertible L] (hL : IsAmple L) :
    ∃ f : X ⟶ Proj (RingedSpace.GradedSections.grading L), IsSectionRingProjMap L f := sorry

end AlgebraicGeometry.Scheme.Modules
