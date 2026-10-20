module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation.Composition
import StacksCheckRecall

/-!
# Composition of separation axioms for morphisms of formal algebraic spaces

Separated and quasi-separated morphisms of formal algebraic spaces are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.30.4 (1): Separated morphisms of formal algebraic spaces are stable
under composition. -/
@[stacks 0ARR] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.separated_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@Separated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)))

#check (AlgebraicGeometry.FormalAlgebraicSpace.separated_comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g], Separated (f ≫ g))

/- Lemma 87.30.4 (2): Quasi-separated morphisms of formal algebraic spaces are
stable under composition. -/
@[stacks 0ARR] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.quasiSeparated_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@QuasiSeparated S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)))

#check (AlgebraicGeometry.FormalAlgebraicSpace.quasiSeparated_comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g],
    QuasiSeparated (f ≫ g))

end AlgebraicGeometry.FormalAlgebraicSpace
