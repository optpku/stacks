/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.ProjectionFormula
import StacksCheckRecall

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

-- Local instance justification (defeq pin): Match the Abelian-induced Preadditive and HasZeroMorphisms instances used by Intersection.number and its HasInjectiveResolutions parameters.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

universe u

/- Lemma 72.18.7 -/
@[stacks 0EDJ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.pullbackNumber_eq_imageNumber :
    ∀ {k : Type u} [Field k]
      {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
      [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
      [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] {d : ℕ}
      (hZdim : dimension Z = d)
      [Abelian X.Modules] [Abelian Y.Modules] [Abelian Z.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
      [hXRes : HasInjectiveResolutions X.Modules]
      [hYRes : HasInjectiveResolutions Y.Modules]
      [hZRes : HasInjectiveResolutions Z.Modules]
      (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
      [∀ j : Fin d, isInvertibleObject ((Modules.pullback f).obj (L j))]
      (toImage : Z ⟶ fZ) (ι : fZ ⟶ X)
      [IsSchemeTheoreticImage (i ≫ f) toImage ι] [IsClosedImmersion ι]
      [IsIntegral fZ] [IsLocallyNoetherian fZ] [Abelian fZ.Modules]
      [hfZRes : HasInjectiveResolutions fZ.Modules] [Dominant toImage]
      [LocallyOfFiniteType toImage],
      AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number i hZdim
        (fun j ↦ (Modules.pullback f).obj (L j)) =
        if hImageDim : dimension fZ = d then
          (Hom.degree toImage : ℚ) *
            AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number ι hImageDim L
        else 0)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.pullbackNumber_eq_zero_of_image_dimension_lt :
  ∀ {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Y.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [hXRes : HasInjectiveResolutions X.Modules]
    [hYRes : HasInjectiveResolutions Y.Modules]
    [hZRes : HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    [∀ j : Fin d, isInvertibleObject ((Modules.pullback f).obj (L j))]
    (toImage : Z ⟶ fZ) (ι : fZ ⟶ X)
    [IsSchemeTheoreticImage (i ≫ f) toImage ι] [IsClosedImmersion ι]
    [IsIntegral fZ] [IsLocallyNoetherian fZ] [Abelian fZ.Modules]
    [hfZRes : HasInjectiveResolutions fZ.Modules] (hImageDim : dimension fZ < d),
    AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number i hZdim
      (fun j ↦ (Modules.pullback f).obj (L j)) = 0)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.pullbackNumber_eq_degree_mul_imageNumber_of_dim_eq :
  ∀ {k : Type u} [Field k]
    {X Y Z fZ : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Y.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [hXRes : HasInjectiveResolutions X.Modules]
    [hYRes : HasInjectiveResolutions Y.Modules]
    [hZRes : HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    [∀ j : Fin d, isInvertibleObject ((Modules.pullback f).obj (L j))]
    (toImage : Z ⟶ fZ) (ι : fZ ⟶ X)
    [IsSchemeTheoreticImage (i ≫ f) toImage ι] [IsClosedImmersion ι]
    [IsIntegral fZ] [IsLocallyNoetherian fZ] [Abelian fZ.Modules]
    [hfZRes : HasInjectiveResolutions fZ.Modules] [Dominant toImage]
    [LocallyOfFiniteType toImage] (hImageDim : dimension fZ = d),
    AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number i hZdim
      (fun j ↦ (Modules.pullback f).obj (L j)) =
      (Hom.degree toImage : ℚ) *
        AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number ι hImageDim L)
