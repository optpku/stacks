/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Composition of Unramified Morphisms

Unramified and G-unramified morphisms are stable under composition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace FormallyUnramified

/-- The composition of two formally unramified morphisms is formally unramified. -/
theorem comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : FormallyUnramified f)
    (hg : FormallyUnramified g) : FormallyUnramified (f ≫ g) := sorry

end FormallyUnramified

/-- The composition of two unramified morphisms is unramified. -/
instance unramified_comp [Unramified f] [Unramified g] :
    Unramified (f ≫ g) :=
  { toFormallyUnramified := MorphismProperty.comp_mem _ f g inferInstance inferInstance
    toLocallyOfFiniteType := inferInstance }

/-- The composition of two G-unramified morphisms is G-unramified. -/
instance gUnramified_comp [GUnramified f] [GUnramified g] :
    GUnramified (f ≫ g) :=
  { toFormallyUnramified := MorphismProperty.comp_mem _ f g inferInstance inferInstance
    toLocallyOfFinitePresentation := inferInstance }

end AlgebraicGeometry
