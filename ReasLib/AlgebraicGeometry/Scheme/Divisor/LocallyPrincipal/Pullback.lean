/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal

/-!
# Pullbacks of locally principal closed subschemes
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme

variable {S S' Z : Scheme.{u}}

/-- The first projection from the pullback of a locally principal closed immersion is locally
principal. -/
instance pullback_fst (f : S' ⟶ S) (i : Z ⟶ S) [IsLocallyPrincipalClosedSubscheme i] :
    IsLocallyPrincipalClosedSubscheme (pullback.fst f i) := sorry

end AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme
