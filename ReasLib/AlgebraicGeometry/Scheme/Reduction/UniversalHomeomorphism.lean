/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties

/-!
# The reduction inclusion as a universal homeomorphism

This file records the surjectivity and universal-homeomorphism properties of
the canonical morphism from the reduction of a scheme.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism from the reduction of a scheme is surjective. -/
theorem surjective_reductionι (X : Scheme.{u}) :
    Surjective (reductionι X) := sorry

/-- The canonical morphism from the reduction of a scheme is a universal homeomorphism. -/
theorem universalHomeomorphism_reductionι (X : Scheme.{u}) :
    UniversalHomeomorphism (reductionι X) := sorry

/-- The reduction inclusion is canonically a universal homeomorphism. -/
instance instUniversalHomeomorphismReductionι (X : Scheme.{u}) :
    UniversalHomeomorphism (reductionι X) :=
  universalHomeomorphism_reductionι X

end AlgebraicGeometry.Scheme
