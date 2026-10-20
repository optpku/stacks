/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.CodimensionOneRamification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Complementary regular stalks provide a discrete-valuation boundary for a dense-open pair. -/
instance hasDVRBoundary_of_regularComplement {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens)
    [h_reg : Fact (∀ x : X, x ∉ (U : Set X) → IsRegularLocalRing (X.presheaf.stalk x))] :
    HasDVRBoundary X U := sorry

/-- A finite étale cover of a dense open extends across regular complementary stalks when it is
unramified in codimension one. -/
theorem exists_extension_of_unramifiedInCodimensionOne {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (hU : Dense (U : Set X))
    [Fact (∀ x : X, x ∉ (U : Set X) → IsRegularLocalRing (X.presheaf.stalk x))]
    (Y : Scheme.FiniteEtale U.toScheme)
    (hY : IsUnramifiedInCodimensionOne U hU Y) :
    ∃ Y' : Scheme.FiniteEtale X, Nonempty ((finiteEtaleBaseChange U.ι).obj Y' ≅ Y) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
