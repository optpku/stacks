/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.Algebra.WLocalHull.Stage

/-!
# Vanishing-pattern stage spectra

The finite-stage affine scheme is the spectrum of the vanishing-pattern stage
algebra, with a canonical morphism from the product of its stratum charts.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- The affine spectrum of the finite vanishing-pattern stage algebra. -/
noncomputable def spectrum (E : Finset A) : Scheme.{u} :=
  Spec (.of (stage A E))

/-- The product of the standard affine charts `(A ⧸ I)_f` of the strata of a finite set. -/
abbrev closedStage (E : Finset A) : Type u :=
  ∀ p : Pattern A E, stratumSections A p.elem p.span

/-- The product of the canonical maps from specializing localizations to stratum charts. -/
noncomputable def closedStageMap (E : Finset A) : stage A E →+* closedStage A E :=
  RingHom.pi fun p ↦ (Localization.Specializing.toAwayQuotient p.elem p.span).comp (stage.eval A p)

/-- The morphism from the spectrum of the closed-stage algebra to the stage spectrum. -/
noncomputable def closedHom (E : Finset A) :
    Spec (.of (closedStage A E)) ⟶ spectrum A E :=
  Spec.map (CommRingCat.ofHom (closedStageMap A E))

end Algebra.WLocalHull
