/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

/-!
# Composition of morphisms representable by algebraic spaces

Representability by algebraic spaces is stable under composition of sheaf
morphisms on a chosen big fppf site.
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry Limits MorphismProperty ChosenBigFppfSite

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- The composite of two sheaf morphisms representable by algebraic spaces on
a chosen big fppf site is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces.comp
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : representableByAlgebraicSpaces f) (hg : representableByAlgebraicSpaces g) :
    representableByAlgebraicSpaces (f ≫ g) :=
  sorry

/-- Representability by algebraic spaces is stable under composition of
sheaf morphisms on a chosen big fppf site. -/
instance representableByAlgebraicSpaces.isStableUnderComposition
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] :
    IsStableUnderComposition
      (fun {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) ↦
        representableByAlgebraicSpaces f) where
  comp_mem f g hf hg := representableByAlgebraicSpaces.comp f g hf hg

end AlgebraicGeometry.ChosenBigFppfSite
