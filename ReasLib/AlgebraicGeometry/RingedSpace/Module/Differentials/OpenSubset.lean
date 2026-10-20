/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of relative differentials to open subsets

Restriction to an open subset is inverse image along its inclusion. This file provides the
open-subset specialization of the canonical inverse-image comparison for relative differentials.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf.RelativeDifferentials.OpenSubset

variable {X : TopCat.{u}} (U : Opens X)
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- The canonical comparison from the restriction of relative differentials to the relative
differentials of the restricted ring-sheaf morphism. -/
noncomputable abbrev comparison (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback
      (InverseImage.structureMap U.inclusion' O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) ⟶
      TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} U.inclusion').map φ) :=
  InverseImage.comparison U.inclusion' φ

/-- The open-subset restriction comparison on relative differentials is an isomorphism. -/
instance comparison_isIso (φ : O₁ ⟶ O₂) : IsIso (comparison U φ) :=
  InverseImage.comparison_isIso U.inclusion' φ

/-- Lemma 17.28.5 (08RQ): restriction to an open subset commutes canonically with relative
differentials. -/
@[stacks 08RQ]
noncomputable abbrev iso (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback
      (InverseImage.structureMap U.inclusion' O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) ≅
      TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} U.inclusion').map φ) :=
  InverseImage.iso U.inclusion' φ

/-- The forward map of the open-subset relative-differentials isomorphism is `comparison`. -/
@[stacks 08RQ "open-subset comparison isomorphism hom", simp]
theorem iso_hom (φ : O₁ ⟶ O₂) :
    (iso U φ).hom = comparison U φ := sorry

/-- The restriction comparison is compatible with the restricted universal derivation. -/
theorem comparison_spec (φ : O₁ ⟶ O₂) :
    (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
      (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.map U.inclusion') φ).IsPullbackDesc (comparison U φ) := sorry

/-- A morphism compatible with the restricted universal derivation is the canonical comparison. -/
theorem eq_comparison (φ : O₁ ⟶ O₂)
    {tau :
      (SheafOfModules.pullback
        (InverseImage.structureMap U.inclusion' O₂)).obj
          (TopCat.Sheaf.relativeDifferentials φ) ⟶
        TopCat.Sheaf.relativeDifferentials
          ((TopCat.Sheaf.pullback CommRingCat.{u} U.inclusion').map φ)}
    (h_tau :
      (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
        (J := Opens.grothendieckTopology X)
        (K := Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        (Opens.map U.inclusion') φ).IsPullbackDesc tau) :
    tau = comparison U φ := sorry

end TopCat.Sheaf.RelativeDifferentials.OpenSubset
