/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Variety
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Composition of flat pullbacks for varieties

This file transports the flat-pullback composition law to the dimension grading intrinsic to
varieties over a field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.CycleGroup

/-- The degree produced by two successive flat pullbacks between varieties equals the degree
obtained by adding the difference between the source and target dimensions. -/
theorem flatPullback_comp_variety_source_degree
    {K : Type u} [Field K]
    (X Y Z : SchemeOverField K) [Variety X] [Variety Y] [Variety Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f.left] [Flat g.left] (k : ℤ) :
    (k + (SchemeOverField.relativeDimensionGap Y Z g : ℤ)) +
        (SchemeOverField.relativeDimensionGap X Y f : ℤ) =
      k + X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
          (genericPoint X.left) -
        Z.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
          (genericPoint Z.left) := sorry

/-- The degree shifted by the sum of the two canonical relative dimensions equals the degree
obtained by adding the difference between the source and target dimensions. -/
theorem flatPullback_comp_variety_composite_degree
    {K : Type u} [Field K]
    (X Y Z : SchemeOverField K) [Variety X] [Variety Y] [Variety Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f.left] [Flat g.left] (k : ℤ) :
    k + ((SchemeOverField.relativeDimensionGap X Y f +
        SchemeOverField.relativeDimensionGap Y Z g : ℕ) : ℤ) =
      k + X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
          (genericPoint X.left) -
        Z.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
          (genericPoint Z.left) := sorry

/-- For composable flat morphisms of varieties, successive pullback of cycles agrees with
pullback along the composite after both maps are transported to the dimension grading of the
source and target varieties. -/
theorem flatPullback_comp_of_varieties
    {K : Type u} [Field K]
    (X Y Z : SchemeOverField K) [Variety X] [Variety Y] [Variety Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f.left] [Flat g.left] (k : ℤ) :
    (reindex (X.hom.relativeDimensionFunction
        (fun _ : Spec (CommRingCat.of K) ↦ 0))
      (flatPullback_comp_variety_source_degree X Y Z f g k)).comp
        ((flatPullback (fun _ : Spec (CommRingCat.of K) ↦ 0) X Y f
          (SchemeOverField.relativeDimensionGap X Y f)
          (k + (SchemeOverField.relativeDimensionGap Y Z g : ℤ))).comp
          (flatPullback (fun _ : Spec (CommRingCat.of K) ↦ 0) Y Z g
            (SchemeOverField.relativeDimensionGap Y Z g) k)) =
      (reindex (X.hom.relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (flatPullback_comp_variety_composite_degree X Y Z f g k)).comp
          (flatPullback (fun _ : Spec (CommRingCat.of K) ↦ 0) X Z (f ≫ g)
            (SchemeOverField.relativeDimensionGap X Y f +
              SchemeOverField.relativeDimensionGap Y Z g) k) := sorry

end AlgebraicGeometry.CycleGroup
