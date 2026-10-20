/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.ClosedImmersion

/-!
# Finite factorizations through morphisms of finite presentation

This module records closed-immersion factorizations of finite morphisms through finite
morphisms of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A finite morphism over a quasi-compact and quasi-separated base factors as a closed
immersion followed by a finite morphism of finite presentation. -/
theorem exists_finite_closedImmersion_factorization_of_isFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (MorphismProperty.comp @IsClosedImmersion
      (@IsFinite ⊓ (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme))) f := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
