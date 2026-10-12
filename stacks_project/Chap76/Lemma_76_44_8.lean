/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap76.Lemma_76_44_3_RegularImmersion

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

/-- Lemma 76.44.8 (1): If `i : Z ⟶ Y` and `j : Y ⟶ X` are Koszul-regular
immersions of algebraic spaces over a scheme `S`, then so is `i ≫ j`. -/
@[stacks 09S0]
instance IsKoszulRegularImmersion.comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsKoszulRegularImmersion i] [IsKoszulRegularImmersion j] :
    IsKoszulRegularImmersion (i ≫ j) :=
  sorry

/-- Lemma 76.44.8 (2): If `i : Z ⟶ Y` and `j : Y ⟶ X` are `H₁`-regular
immersions of algebraic spaces over a scheme `S`, then so is `i ≫ j`. -/
@[stacks 09S0]
instance IsH1RegularImmersion.comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsH1RegularImmersion j] :
    IsH1RegularImmersion (i ≫ j) :=
  sorry

/-- Lemma 76.44.8 (3): If `i : Z ⟶ Y` is an `H₁`-regular immersion of
algebraic spaces over a scheme `S` and `j : Y ⟶ X` is a quasi-regular
immersion, then `i ≫ j` is a quasi-regular immersion. -/
@[stacks 09S0]
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
