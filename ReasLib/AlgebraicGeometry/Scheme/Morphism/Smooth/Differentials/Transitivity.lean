/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity of Differentials for Smooth Scheme Morphisms

For composable scheme morphisms `X ⟶ Y ⟶ S`, smoothness of `X ⟶ Y` makes the canonical
transitivity complex of relative differentials short exact.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- If `f : X ⟶ Y` is smooth, then the canonical transitivity complex

`f^* Ω[Y/S] ⟶ Ω[X/S] ⟶ Ω[X/Y]`

is short exact. -/
@[stacks 02K4]
theorem Smooth.relativeDifferentialsTransitivity_shortExact
    (f : X ⟶ Y) (g : Y ⟶ S) [Smooth f] :
    (RingedSpace.Hom.Differentials.Transitivity.complex
      f.toShHom g.toShHom).ShortExact := sorry

end AlgebraicGeometry
