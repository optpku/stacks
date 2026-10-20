module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications

/-!
# Composition of regular immersions of algebraic spaces

Koszul-regular and `H₁`-regular immersions of algebraic spaces are stable under
composition. An `H₁`-regular immersion followed by a quasi-regular immersion is
quasi-regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The composite of two Koszul-regular immersions of algebraic spaces over a
scheme is a Koszul-regular immersion. -/
instance IsKoszulRegularImmersion.comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsKoszulRegularImmersion i] [IsKoszulRegularImmersion j] :
    IsKoszulRegularImmersion (i ≫ j) :=
  sorry

/-- The composite of two `H₁`-regular immersions of algebraic spaces over a
scheme is an `H₁`-regular immersion. -/
instance IsH1RegularImmersion.comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsH1RegularImmersion j] :
    IsH1RegularImmersion (i ≫ j) :=
  sorry

/-- An `H₁`-regular immersion of algebraic spaces followed by a quasi-regular
immersion is a quasi-regular immersion. -/
instance IsQuasiRegularImmersion.comp_of_isH1RegularImmersion
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsQuasiRegularImmersion j] :
    IsQuasiRegularImmersion (i ≫ j) :=
  sorry

/-- Koszul-regular immersions of algebraic spaces over `S` are stable under
composition. -/
instance IsKoszulRegularImmersion.instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsKoszulRegularImmersion S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- `H₁`-regular immersions of algebraic spaces over `S` are stable under
composition. -/
instance IsH1RegularImmersion.instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsH1RegularImmersion S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
