/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat

/-!
# Universal openness of syntomic morphisms

Syntomic scheme morphisms are universally open.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Syntomic

/-- A syntomic morphism of schemes is universally open. -/
theorem universallyOpen (hf : Syntomic f) : UniversallyOpen f := sorry

end Syntomic

end AlgebraicGeometry
