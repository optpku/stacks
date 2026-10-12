/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Universal openness of smooth morphisms

Smooth scheme morphisms are universally open.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Smooth

/-- A smooth morphism of schemes is universally open. -/
theorem universallyOpen (hf : Smooth f) : UniversallyOpen f := sorry

end Smooth

end AlgebraicGeometry
