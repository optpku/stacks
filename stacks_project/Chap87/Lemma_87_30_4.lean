module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap87.Definition_87_30_1_Separation

/-!
# Composition of separation axioms for morphisms of formal algebraic spaces

Separated and quasi-separated morphisms of formal algebraic spaces are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.30.4 (1): Separated morphisms of formal algebraic spaces are stable
under composition. -/
@[stacks 0ARR]
instance separated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Separated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- The composition of separated morphisms of formal algebraic spaces is
separated. -/
instance separated_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g] :
    Separated (f ≫ g) := sorry

/-- Lemma 87.30.4 (2): Quasi-separated morphisms of formal algebraic spaces are
stable under composition. -/
@[stacks 0ARR]
instance quasiSeparated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiSeparated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- The composition of quasi-separated morphisms of formal algebraic spaces is
quasi-separated. -/
instance quasiSeparated_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
