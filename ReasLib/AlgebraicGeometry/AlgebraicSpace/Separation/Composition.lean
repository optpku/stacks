module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of separation axioms for morphisms of algebraic spaces

Separated, locally separated, and quasi-separated morphisms of algebraic
spaces are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Separated morphisms of algebraic spaces are stable under composition. -/
instance separated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Separated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of separated morphisms of algebraic spaces is separated. -/
instance separated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g] :
    Separated (f ≫ g) :=
  MorphismProperty.comp_mem (@Separated S) f g inferInstance inferInstance

/-- Locally separated morphisms of algebraic spaces are stable under composition. -/
instance locallySeparated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of locally separated morphisms of algebraic spaces is locally
separated. -/
instance locallySeparated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallySeparated f] [LocallySeparated g] :
    LocallySeparated (f ≫ g) :=
  MorphismProperty.comp_mem (@LocallySeparated S) f g inferInstance inferInstance

/-- Quasi-separated morphisms of algebraic spaces are stable under composition. -/
instance quasiSeparated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of quasi-separated morphisms of algebraic spaces is
quasi-separated. -/
instance quasiSeparated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  MorphismProperty.comp_mem (@QuasiSeparated S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
