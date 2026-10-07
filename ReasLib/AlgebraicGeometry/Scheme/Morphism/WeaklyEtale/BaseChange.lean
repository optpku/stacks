module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Diagonal.BaseChange

/-!
# Weakly étale morphisms under base change

This module records that weak étaleness of scheme morphisms is preserved by canonical base
change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- Weak étaleness of a scheme morphism is preserved by canonical base change. -/
theorem baseChange {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : WeaklyEtale f) : WeaklyEtale (pullback.fst g f) := sorry

end AlgebraicGeometry.WeaklyEtale
