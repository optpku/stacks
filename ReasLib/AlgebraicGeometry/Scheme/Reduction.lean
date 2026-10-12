/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced

/-!
# Scheme-theoretic reduction

This file supplies the canonical instances attached to the explicit
nilradical-subsheme construction owned in `ClosedSubscheme.Reduced`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical inclusion of the reduction of a scheme is a closed immersion. -/
@[stacks 01J4 "reduction closed immersion"]
theorem isClosedImmersion_reductionι (X : Scheme.{u}) :
    IsClosedImmersion (reductionι X) := sorry

attribute [instance] isClosedImmersion_reductionι

/-- The reduction of a scheme is reduced. -/
@[stacks 01J4 "reduction is reduced"]
instance instIsReducedReduction (X : Scheme.{u}) :
    IsReduced (reduction X) := sorry

/-- The reduction inclusion of a reduced scheme is an isomorphism. -/
@[stacks 01J4 "reduction of a reduced scheme"]
theorem reductionι_isIso (X : Scheme.{u}) [IsReduced X] :
    IsIso (reductionι X) := sorry

/-- The reduction inclusion of a reduced scheme is canonically an isomorphism. -/
instance instIsIsoReductionι (X : Scheme.{u}) [IsReduced X] :
    IsIso (reductionι X) :=
  reductionι_isIso X

end AlgebraicGeometry.Scheme
