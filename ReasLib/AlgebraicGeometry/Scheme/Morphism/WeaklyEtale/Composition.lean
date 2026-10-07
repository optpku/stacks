module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Diagonal

/-!
# Composition of weakly étale morphisms

This module records closure of weakly étale scheme morphisms under composition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- The composite of two weakly étale scheme morphisms is weakly étale. -/
theorem comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : WeaklyEtale f) (hg : WeaklyEtale g) :
    WeaklyEtale (f ≫ g) := sorry

end AlgebraicGeometry.WeaklyEtale
