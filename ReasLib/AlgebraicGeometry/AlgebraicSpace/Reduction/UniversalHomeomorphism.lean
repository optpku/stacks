/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# The reduction inclusion as a universal homeomorphism of algebraic spaces

The canonical closed immersion from the reduction of an algebraic space is a
universal homeomorphism.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical closed immersion from the reduction of an algebraic space is a
universal homeomorphism. -/
instance instUniversalHomeomorphism_reductionι {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversalHomeomorphism (reductionι X) := sorry

end AlgebraicGeometry.AlgebraicSpace
