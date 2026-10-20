/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.FunctionFieldDegree

/-!
# Projection formula for numerical intersections

This file relates numerical intersections after pullback to the corresponding
intersection on the scheme-theoretic image.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- If the image of an integral closed subscheme has smaller dimension, its numerical
intersection with a pulled-back family of invertible modules vanishes. -/
theorem pullbackNumber_eq_zero_of_image_topologicalKrullDim_lt
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} [IsProper X.hom] [IsProper Y.hom]
    (f : Y ⟶ X) (Z : Y.left.IdealSheafData) [IsIntegral Z.subscheme]
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
    (L : Fin d → X.left.Modules) [∀ j : Fin d, Invertible (L j)]
    (hImageDim : topologicalKrullDim (Scheme.Hom.image (Z.subschemeι ≫ f.left)) < d) :
    number k Y.hom Z hZdim (fun j ↦ (Scheme.Modules.pullback f.left).obj (L j)) = 0 := sorry

/-- If an integral closed subscheme and its scheme-theoretic image have the same dimension,
pullback multiplies the image intersection number by the induced function-field degree. -/
theorem pullbackNumber_eq_degree_mul_imageNumber_of_dim_eq
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} [IsProper X.hom] [IsProper Y.hom]
    (f : Y ⟶ X) (Z : Y.left.IdealSheafData) [IsIntegral Z.subscheme]
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    [HasExt
      (Sheaf
        (Opens.grothendieckTopology
          (Scheme.Hom.image (Z.subschemeι ≫ f.left)).carrier)
        AddCommGrpCat.{u})]
    {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
    (L : Fin d → X.left.Modules) [∀ j : Fin d, Invertible (L j)]
    (hImageDim : topologicalKrullDim (Scheme.Hom.image (Z.subschemeι ≫ f.left)) = d) :
    number k Y.hom Z hZdim (fun j ↦ (Scheme.Modules.pullback f.left).obj (L j)) =
      ((Scheme.Hom.toImage (Z.subschemeι ≫ f.left)).inducedFunctionFieldDegree : ℚ) *
        number k X.hom ((Z.subschemeι ≫ f.left).ker) hImageDim L := sorry

/-- Numerical intersection after pullback is the induced function-field degree times the
intersection on the scheme-theoretic image when dimensions agree, and is zero otherwise. -/
theorem pullbackNumber_eq_imageNumber
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} [IsProper X.hom] [IsProper Y.hom]
    (f : Y ⟶ X) (Z : Y.left.IdealSheafData) [IsIntegral Z.subscheme]
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    [HasExt
      (Sheaf
        (Opens.grothendieckTopology
          (Scheme.Hom.image (Z.subschemeι ≫ f.left)).carrier)
        AddCommGrpCat.{u})]
    {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
    (L : Fin d → X.left.Modules) [∀ j : Fin d, Invertible (L j)] :
    number k Y.hom Z hZdim (fun j ↦ (Scheme.Modules.pullback f.left).obj (L j)) =
      if hImageDim :
          topologicalKrullDim (Scheme.Hom.image (Z.subschemeι ≫ f.left)) = d then
        ((Scheme.Hom.toImage (Z.subschemeι ≫ f.left)).inducedFunctionFieldDegree : ℚ) *
          number k X.hom ((Z.subschemeι ≫ f.left).ker) hImageDim L
      else 0 := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
