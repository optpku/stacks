/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection
public import stacks_project.Chap76.Lemma_76_15_15_Transitivity

/-!
# Conormal transitivity for local complete intersection morphisms of algebraic spaces

For formally unramified morphisms `Z ⟶ Y ⟶ X` of algebraic spaces over a
scheme `S`, if `Z ⟶ Y` is a local complete intersection, the canonical
conormal transitivity sequence is short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
namespace Transitivity

variable {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
variable (i : Z ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
variable [FormallyUnramified i] [IsLocalCompleteIntersection i]
variable (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X))

/-- Lemma 76.48.13: Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be formally unramified
morphisms of algebraic spaces over `S`. Assume that `Z ⟶ Y` is a local complete
intersection morphism. Then the canonical conormal transitivity sequence
`complex iZ fZ iY fY i sq` of Lemma 76.15.15, with maps `baseChange` and
`projection`, namely `0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`, is short
exact. The source citation of Lemma 76.5.6 is the immersion special case of
this formally unramified sequence. -/
@[stacks 06CC]
theorem shortExact_of_isLocalCompleteIntersection :
    (complex iZ fZ iY fY i sq).ShortExact :=
  sorry

/-- For formally unramified `Z ⟶ Y ⟶ X` with `Z ⟶ Y` a local complete
intersection, the comparison `baseChange` is a monomorphism. -/
instance mono_baseChange : Mono (baseChange iZ fZ iY fY i sq) :=
  sorry

end Transitivity
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
