/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_44_3_RegularImmersion
public import stacks_project.Chap76.Lemma_76_44_10_Transitivity

/-!
# Conormal transitivity for H₁-regular immersions of algebraic spaces

If `i : Z ⟶ Y` is an `H₁`-regular immersion of algebraic spaces over a scheme
`S` and `j : Y ⟶ X` is an immersion, then the canonical conormal transitivity
sequence of Lemma 76.5.6 is short exact and étale-locally split.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

namespace IsH1RegularImmersion

/-- Lemma 76.44.7: Let `S` be a scheme. Let `i : Z ⟶ Y` and `j : Y ⟶ X` be
immersions of algebraic spaces over `S`. Assume that `i` is `H₁`-regular.
Then the canonical sequence `complex i j` of Lemma 76.5.6, with maps
`baseChange i j` and `projection i j`,
`0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`, is exact and étale-locally
split. -/
@[stacks 09RZ]
theorem conormalTransitivity_isShortExactLocallySplit
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsImmersion j] :
    IsShortExactLocallySplit i j :=
  sorry

/-- The canonical conormal transitivity complex of an `H₁`-regular immersion
followed by an immersion of algebraic spaces is short exact. -/
theorem conormalTransitivity_shortExact
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsImmersion j] :
    (complex i j).ShortExact :=
  sorry

/-- For an `H₁`-regular immersion followed by an immersion of algebraic spaces,
the comparison `baseChange i j` is a monomorphism. -/
instance mono_conormalTransitivity_baseChange
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsImmersion j] :
    Mono (baseChange i j) :=
  sorry

end IsH1RegularImmersion

end AlgebraicGeometry.AlgebraicSpace
