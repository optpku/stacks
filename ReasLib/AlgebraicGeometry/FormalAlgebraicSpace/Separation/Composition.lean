/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

/-!
# Composition of separation conditions for morphisms of presheaves

Separated and quasi-separated morphisms of presheaves over a scheme are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Separated morphisms of presheaves over a scheme are stable under composition. -/
instance separated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Separated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- The composition of separated morphisms of presheaves over a scheme is separated. -/
instance separated_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g] :
    Separated (f ≫ g) :=
  MorphismProperty.comp_mem (@Separated S) f g inferInstance inferInstance

/-- Quasi-separated morphisms of presheaves over a scheme are stable under composition. -/
instance quasiSeparated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiSeparated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- The composition of quasi-separated morphisms of presheaves over a scheme is
quasi-separated. -/
instance quasiSeparated_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  MorphismProperty.comp_mem (@QuasiSeparated S) f g inferInstance inferInstance

end AlgebraicGeometry.FormalAlgebraicSpace
