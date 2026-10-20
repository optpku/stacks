/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Proper

/-!
# Function-field degrees of scheme-theoretic images

This file records dominance and finiteness properties of the canonical map to
the scheme-theoretic image of a closed subscheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map from a closed subscheme of a proper scheme to its image under a
morphism between schemes proper over the same base is surjective. -/
instance instSurjectiveToImageOfClosedSubschemeProperOver
    {S : Scheme.{u}} {X Y : Over S} [IsProper X.hom] [IsProper Y.hom]
    (f : Y ⟶ X) (Z : Y.left.IdealSheafData) :
    Surjective (toImage (Z.subschemeι ≫ f.left)) := sorry

/-- If an integral closed subscheme and its scheme-theoretic image under a morphism of
proper schemes over a field have the same dimension, the canonical map to the image induces
a finite extension of function fields. -/
theorem finiteFunctionFieldExtension_toImage_of_image_topologicalKrullDim_eq
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} [IsProper X.hom] [IsProper Y.hom]
    (f : Y ⟶ X) (Z : Y.left.IdealSheafData) [IsIntegral Z.subscheme]
    {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
    (hImageDim : topologicalKrullDim (image (Z.subschemeι ≫ f.left)) = d) :
    (toImage (Z.subschemeι ≫ f.left)).FiniteFunctionFieldExtension := sorry

end AlgebraicGeometry.Scheme.Hom
