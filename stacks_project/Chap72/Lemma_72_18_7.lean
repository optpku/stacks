module

public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap72.Definition_72_5_2
public import stacks_project.Chap72.Definition_72_18_3_Number

/-!
# Lemma 72.18.7

Pullback of invertible modules multiplies the intersection number on the
scheme-theoretic image by the degree of `Z ⟶ f(Z)`, or vanishes if the image
dimension drops.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 72.18.7: Let `k` be a field. Let `f : Y ⟶ X` be a morphism of algebraic
spaces proper over `k`. Let `Z ⊂ Y` be an integral closed subspace of dimension
`d` and let `L 0, …, L (d - 1)` be invertible `𝒪_X`-modules. Then
`(f^* L 0 ⋯ f^* L (d - 1) · Z) = deg(f|_Z : Z ⟶ f(Z)) (L 0 ⋯ L (d - 1) · f(Z))`,
where `deg(Z ⟶ f(Z))` is `Hom.degree` as in Definition 72.5.2, or `0` if
`dimension f(Z) < d`. Here `f(Z)` is a scheme-theoretic image of `i ≫ f`. -/
@[stacks 0EDJ]
theorem pullbackNumber_eq_imageNumber {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (toBase X)] [Proper (toBase Y)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Y.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    [∀ j : Fin d, isInvertibleObject ((Modules.pullback f).obj (L j))]
    (toImage : Z ⟶ fZ) (ι : fZ ⟶ X)
    [IsSchemeTheoreticImage (i ≫ f) toImage ι] [IsClosedImmersion ι]
    [IsIntegral fZ] [IsLocallyNoetherian fZ] [Abelian fZ.Modules]
    [HasInjectiveResolutions fZ.Modules] [Dominant toImage]
    [LocallyOfFiniteType toImage] :
    number i hZdim (fun j ↦ (Modules.pullback f).obj (L j)) =
      if hImageDim : dimension fZ = d then
        (Hom.degree toImage : ℚ) * number ι hImageDim L
      else 0 := sorry

/-- If an integral closed subspace has scheme-theoretic image of smaller
dimension, its numerical intersection with a pulled-back family of invertible
modules vanishes. -/
theorem pullbackNumber_eq_zero_of_image_dimension_lt {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (toBase X)] [Proper (toBase Y)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Y.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    [∀ j : Fin d, isInvertibleObject ((Modules.pullback f).obj (L j))]
    (toImage : Z ⟶ fZ) (ι : fZ ⟶ X)
    [IsSchemeTheoreticImage (i ≫ f) toImage ι] [IsClosedImmersion ι]
    [IsIntegral fZ] [IsLocallyNoetherian fZ] [Abelian fZ.Modules]
    [HasInjectiveResolutions fZ.Modules] (hImageDim : dimension fZ < d) :
    number i hZdim (fun j ↦ (Modules.pullback f).obj (L j)) = 0 := sorry

/-- If an integral closed subspace and its scheme-theoretic image have the same
dimension, pullback multiplies the image intersection number by `Hom.degree` of
`Z ⟶ f(Z)`. -/
theorem pullbackNumber_eq_degree_mul_imageNumber_of_dim_eq {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (toBase X)] [Proper (toBase Y)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Y.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    [∀ j : Fin d, isInvertibleObject ((Modules.pullback f).obj (L j))]
    (toImage : Z ⟶ fZ) (ι : fZ ⟶ X)
    [IsSchemeTheoreticImage (i ≫ f) toImage ι] [IsClosedImmersion ι]
    [IsIntegral fZ] [IsLocallyNoetherian fZ] [Abelian fZ.Modules]
    [HasInjectiveResolutions fZ.Modules] [Dominant toImage]
    [LocallyOfFiniteType toImage] (hImageDim : dimension fZ = d) :
    number i hZdim (fun j ↦ (Modules.pullback f).obj (L j)) =
      (Hom.degree toImage : ℚ) * number ι hImageDim L := sorry

end Intersection
end AlgebraicGeometry.AlgebraicSpace.Modules
