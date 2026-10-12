/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap76.Definition_76_44_2_RegularImmersion
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Koszul-regular immersions from étale charts into a smooth space

An étale-local immersion of algebraic spaces into a space smooth over `Y` is
Koszul-regular when the structure morphism `X ⟶ Y` is a local complete
intersection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsKoszulRegularImmersion

/-- Lemma 76.48.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Let `P` be an algebraic
space smooth over `Y`. Let `U ⟶ X` be an étale morphism of algebraic spaces
and let `i : U ⟶ P` be an immersion of algebraic spaces over `Y`. Then `i` is
a Koszul-regular immersion of algebraic spaces. -/
@[stacks 06C5]
theorem of_localCompleteIntersection_over_smooth {S : Scheme.{u}}
    {X Y P U : AlgebraicSpace S} (f : X ⟶ Y) (p : P ⟶ Y) (u : U ⟶ X) (i : U ⟶ P)
    [IsLocalCompleteIntersection f] [Smooth p] [Etale u] [IsImmersion i]
    (h_over : i ≫ p = u ≫ f) : IsKoszulRegularImmersion i :=
  sorry

end IsKoszulRegularImmersion

end AlgebraicGeometry.AlgebraicSpace
