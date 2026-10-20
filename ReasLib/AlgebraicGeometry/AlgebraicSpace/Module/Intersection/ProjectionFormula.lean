/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Degree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage

/-!
# Projection formula for numerical intersections

Numerical intersections of pulled-back invertible modules are determined by the
scheme-theoretic image and the degree of the induced morphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

-- Local instance justification (defeq pin): Match the Abelian-induced Preadditive and HasZeroMorphisms instances used by Intersection.number and its HasInjectiveResolutions parameters.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The intersection number of pulled-back invertible modules is the degree of
the map to the scheme-theoretic image times the image intersection number when
the image has the same dimension, and is zero otherwise. -/
theorem pullbackNumber_eq_imageNumber {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
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

/-- A pulled-back intersection number vanishes when the scheme-theoretic image
has smaller dimension than the source subspace. -/
theorem pullbackNumber_eq_zero_of_image_dimension_lt {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
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

/-- When the source subspace and its scheme-theoretic image have equal
dimension, pullback multiplies the image intersection number by the degree. -/
theorem pullbackNumber_eq_degree_mul_imageNumber_of_dim_eq {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
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

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
