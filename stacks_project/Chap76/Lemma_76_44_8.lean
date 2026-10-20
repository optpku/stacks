module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Composition
import StacksCheckRecall

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

/- Lemma 76.44.8 (1): If `i : Z ⟶ Y` and `j : Y ⟶ X` are Koszul-regular
immersions of algebraic spaces over a scheme `S`, then so is `i ≫ j`. -/
@[stacks 09S0]
#check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.comp :
  ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsKoszulRegularImmersion i] [IsKoszulRegularImmersion j],
    IsKoszulRegularImmersion (i ≫ j))

/- Lemma 76.44.8 (2): If `i : Z ⟶ Y` and `j : Y ⟶ X` are `H₁`-regular
immersions of algebraic spaces over a scheme `S`, then so is `i ≫ j`. -/
@[stacks 09S0]
#check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.comp :
  ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsH1RegularImmersion j],
    IsH1RegularImmersion (i ≫ j))

/- Lemma 76.44.8 (3): If `i : Z ⟶ Y` is an `H₁`-regular immersion of
algebraic spaces over a scheme `S` and `j : Y ⟶ X` is a quasi-regular
immersion, then `i ≫ j` is a quasi-regular immersion. -/
@[stacks 09S0]
#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.comp_of_isH1RegularImmersion :
  ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsQuasiRegularImmersion j],
    IsQuasiRegularImmersion (i ≫ j))

#check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.instIsStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@IsKoszulRegularImmersion S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.instIsStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@IsH1RegularImmersion S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
