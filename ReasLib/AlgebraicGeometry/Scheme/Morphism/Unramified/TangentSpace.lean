/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Map
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

/-!
# Tangent-space criterion for unramified morphisms

This file relates injectivity of relative tangent maps to pointwise unramifiedness.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a composable pair of scheme morphisms whose composite is locally of finite type, if the
induced residue-field map at a point is bijective, then the relative tangent map is injective if
and only if the first morphism is unramified at that point. -/
theorem injective_relativeTangentMapAt_iff_unramifiedAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    [LocallyOfFiniteType (f ≫ g)]
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom) :
    Function.Injective (relativeTangentMapAt f g x hκ) ↔ f.UnramifiedAt x := sorry

end AlgebraicGeometry.Scheme.Hom
