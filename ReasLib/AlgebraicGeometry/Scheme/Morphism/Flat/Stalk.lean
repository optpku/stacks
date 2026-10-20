/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.FlatOverAt
public import ReasLib.RingTheory.EssentialFiniteness.Basic

/-!
# Essential finite presentation of stalk maps

This file relates pointwise flatness and local finite type for scheme morphisms to essential
finite presentation of the induced maps on local rings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type scheme morphism that is flat at a point induces an essentially finitely
presented map on local rings at that point. -/
@[stacks 05I8]
theorem essFinitePresentation_stalkMap_of_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (h_flat : f.flatAt x) :
    (f.stalkMap x).hom.EssFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Hom
