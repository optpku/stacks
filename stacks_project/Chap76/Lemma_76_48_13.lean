module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.ConormalTransitivity
import StacksCheckRecall

/-!
# Conormal transitivity for local complete intersection morphisms of algebraic spaces

For formally unramified morphisms `Z ⟶ Y ⟶ X` of algebraic spaces over a
scheme `S`, if `Z ⟶ Y` is a local complete intersection, the canonical
conormal transitivity sequence is short exact.

The canonical sequence `complex iZ fZ iY fY i sq` of Lemma 76.15.15 has maps
`baseChange` and `projection`, namely
`0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`.
The source citation of Lemma 76.5.6 is the immersion special case of this
formally unramified sequence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.48.13: Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be formally unramified
morphisms of algebraic spaces over `S`. Assume that `Z ⟶ Y` is a local complete
intersection morphism. Then the canonical conormal transitivity sequence
`complex iZ fZ iY fY i sq` of Lemma 76.15.15, with maps `baseChange` and
`projection`, namely `0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`, is short
exact. The source citation of Lemma 76.5.6 is the immersion special case of
this formally unramified sequence. -/
@[stacks 06CC]
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Transitivity.shortExact_of_isLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
    (i : Z ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
    [FormallyUnramified i] [IsLocalCompleteIntersection i]
    (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X)),
    (IsUniversalFirstOrder.Transitivity.complex iZ fZ iY fY i sq).ShortExact)

#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Transitivity.mono_baseChange :
  ∀ {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
    (i : Z ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
    [FormallyUnramified i] [IsLocalCompleteIntersection i]
    (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X)),
    Mono (IsUniversalFirstOrder.Transitivity.baseChange iZ fZ iY fY i sq))
