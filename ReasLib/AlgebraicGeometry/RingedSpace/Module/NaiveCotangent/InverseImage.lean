/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of naive cotangent complexes on topological spaces

The construction is owned for continuous functors of sites. This file gives the opens-site
specialization for a continuous map of topological spaces.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf.NaiveCotangent.InverseImage

variable {X Y : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- The inverse image of the source naive cotangent complex along a continuous map. -/
@[stacks 08TM "opens-site inverse-image source complex"]
abbrev source (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :=
  SheafOfModules.RingedSite.NaiveCotangent.InverseImage.source
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The naive cotangent complex of the inverse-image ring map. -/
@[stacks 08TM "opens-site inverse-image target complex"]
abbrev target (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :=
  SheafOfModules.RingedSite.NaiveCotangent.InverseImage.target
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The explicit comparison from the inverse image of a naive cotangent complex to the naive
cotangent complex of the inverse-image ring map. -/
@[stacks 08TM "opens-site comparison morphism"]
noncomputable abbrev comparison (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    source f φ ⟶ target f φ :=
  SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.map
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The opens-site inverse-image comparison is an isomorphism. -/
@[stacks 08TM "opens-site comparison is an isomorphism"]
instance comparison_isIso (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIso (comparison f φ) := sorry

/-- The named inverse of the opens-site naive-cotangent comparison. -/
@[stacks 08TM "opens-site inverse comparison morphism"]
noncomputable abbrev comparisonInv (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    target f φ ⟶ source f φ :=
  SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.mapInv
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The opens-site comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "opens-site comparison forward-inverse law"]
theorem comparison_hom_inv_id (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    comparison f φ ≫ comparisonInv f φ = 𝟙 _ := sorry

/-- The named inverse followed by the opens-site comparison is the identity. -/
@[simp, stacks 08TM "opens-site comparison inverse-forward law"]
theorem comparison_inv_hom_id (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    comparisonInv f φ ≫ comparison f φ = 𝟙 _ := sorry

/-- Lemma 17.31.3 (08TM): the explicit opens-site comparison from inverse image of a naive
cotangent complex to the naive cotangent complex of the inverse-image ring map. -/
@[stacks 08TM "opens-site comparison isomorphism"]
noncomputable def comparisonIso (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    source f φ ≅ target f φ :=
  SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.iso
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The forward map of the opens-site comparison isomorphism is the explicit comparison. -/
@[simp]
theorem comparisonIso_hom (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparisonIso f φ).hom = comparison f φ := sorry

/-- The degree-`n` component of the opens-site comparison isomorphism is the generic
degreewise comparison. -/
@[stacks 08TM "opens-site degreewise inverse-image comparison", simp]
theorem comparisonIso_hom_f (f : Y ⟶ X) (φ : O₁ ⟶ O₂) (n : ℤ) :
    (comparisonIso f φ).hom.f n =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.app
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ n := sorry

/-- The inverse map of the opens-site comparison isomorphism is the categorical inverse of the
explicit comparison. -/
@[stacks 08TM "opens-site inverse comparison morphism", simp]
theorem comparisonIso_inv (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparisonIso f φ).inv = comparisonInv f φ := sorry

/-- The degree-`n` component of the inverse opens-site comparison is the inverse of the generic
degreewise comparison. -/
@[stacks 08TM "opens-site degreewise inverse comparison", simp]
theorem comparisonIso_inv_f (f : Y ⟶ X) (φ : O₁ ⟶ O₂) (n : ℤ) :
    (comparisonIso f φ).inv.f n =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.appInv
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ n := sorry

/-- In degree `-1`, the forward opens-site comparison is the conormal comparison. -/
@[stacks 08TM "opens-site degree -1 comparison"]
theorem comparisonIso_hom_f_negOne (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparisonIso f φ).hom.f (-1) =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Conormal.map
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ := sorry

/-- In degree `0`, the forward opens-site comparison is the differential-term comparison. -/
@[stacks 08TM "opens-site degree 0 comparison"]
theorem comparisonIso_hom_f_zero (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparisonIso f φ).hom.f 0 =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Differentials.map
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ := sorry

/-- In degree `-1`, the inverse opens-site comparison is the inverse conormal comparison. -/
@[stacks 08TM "opens-site degree -1 inverse comparison"]
theorem comparisonIso_inv_f_negOne (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparisonIso f φ).inv.f (-1) =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Conormal.mapInv
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ := sorry

/-- In degree `0`, the inverse opens-site comparison is the inverse differential-term
comparison. -/
@[stacks 08TM "opens-site degree 0 inverse comparison"]
theorem comparisonIso_inv_f_zero (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparisonIso f φ).inv.f 0 =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Differentials.mapInv
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ := sorry

/-- The degree-`n` component of the opens-site comparison is the generic degreewise
comparison. -/
theorem comparison_f (f : Y ⟶ X) (φ : O₁ ⟶ O₂) (n : ℤ) :
    (comparison f φ).f n =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.app
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ n := sorry

/-- The degree `-1` component of the opens-site comparison is its conormal comparison. -/
theorem comparison_f_negOne (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparison f φ).f (-1) =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Conormal.map
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ := sorry

/-- The degree `0` component of the opens-site comparison is its differential comparison. -/
theorem comparison_f_zero (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparison f φ).f 0 =
      SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Differentials.map
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ := sorry

end TopCat.Sheaf.NaiveCotangent.InverseImage
