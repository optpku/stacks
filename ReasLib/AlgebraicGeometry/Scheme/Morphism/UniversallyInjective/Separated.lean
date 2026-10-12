/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Universally injective morphisms are separated

This file records the separation consequence of universal injectivity for scheme morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A universally injective morphism of schemes is separated. -/
instance universallyInjective_isSeparated
    {X S : Scheme.{u}} {f : X ⟶ S} [UniversallyInjective f] :
    IsSeparated f :=
  isSeparated_of_injective f f.injective

end AlgebraicGeometry
