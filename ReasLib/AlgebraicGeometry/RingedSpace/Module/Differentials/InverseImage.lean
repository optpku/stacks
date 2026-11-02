/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of relative differentials on topological spaces

The construction is owned for arbitrary continuous functors of sites.  This file gives the
opens-site specialization for a continuous map of topological spaces.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

namespace TopCat.Sheaf.RelativeDifferentials.InverseImage

variable {X Y : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- The ring-sheaf structure map defining module inverse image along `f`. -/
abbrev structureMap (f : Y ⟶ X) (O : X.Sheaf CommRingCat.{u}) :=
  SheafOfModules.RingedSite.InverseImage.structureMap
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) O

open PresheafOfModules.DifferentialsConstruction

-- Sheafification transports the universal property of the presheaf differentials.
private theorem differentialDesc_fac (φ : O₁ ⟶ O₂)
    {M : SheafOfModules.{u} (ringSheaf (Opens.grothendieckTopology X) O₂)}
    (D : SheafOfModules.RelativeDerivation
      (J := Opens.grothendieckTopology X) φ M) :
    (TopCat.Sheaf.relativeDifferential φ).postcomp
      (TopCat.Sheaf.relativeDifferentialDesc φ D).val = D := by
  change (derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 (ringSheaf (Opens.grothendieckTopology X) O₂).obj))
        ((PresheafOfModules.sheafificationHomEquiv
          (𝟙 (ringSheaf (Opens.grothendieckTopology X) O₂).obj)).symm
            ((isUniversal' φ.hom).desc D))) = D
  rw [Equiv.apply_symm_apply]
  exact (isUniversal' φ.hom).fac D

private theorem differential_postcomp_injective (φ : O₁ ⟶ O₂)
    {M : SheafOfModules.{u} (ringSheaf (Opens.grothendieckTopology X) O₂)}
    {g h : TopCat.Sheaf.relativeDifferentials φ ⟶ M}
    (eq : (TopCat.Sheaf.relativeDifferential φ).postcomp g.val =
      (TopCat.Sheaf.relativeDifferential φ).postcomp h.val) : g = h := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (ringSheaf (Opens.grothendieckTopology X) O₂).obj)).injective
  apply (isUniversal' φ.hom).postcomp_injective
  exact eq

/-- The canonical comparison from the inverse image of relative differentials to the relative
differentials of the inverse-image ring map. -/
@[stacks 08RR "opens-site inverse-image differential comparison"]
noncomputable abbrev comparison (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback (structureMap f O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) ⟶
      TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.comparison
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

private theorem comparison_spec_aux (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ).IsPullbackDesc
        (comparison f φ) := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction
    (structureMap f O₂)
  let D := SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ
  change (TopCat.Sheaf.relativeDifferential φ).postcomp
    ((adj.homEquiv _ _) ((adj.homEquiv _ _).symm
      (TopCat.Sheaf.relativeDifferentialDesc φ D))).val = D
  rw [Equiv.apply_symm_apply]
  exact differentialDesc_fac φ D

private theorem comparison_laws (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (comparison f φ ≫
      SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ = 𝟙 _) ∧
    (SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ ≫
      comparison f φ = 𝟙 _) := by
  let alpha := structureMap f O₂
  let adj := SheafOfModules.pullbackPushforwardAdjunction alpha
  let φ' := (TopCat.Sheaf.pullback CommRingCat.{u} f).map φ
  let c := comparison f φ
  let v := SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ
  let d := TopCat.Sheaf.relativeDifferential φ
  let d' := TopCat.Sheaf.relativeDifferential φ'
  let D := SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ
  let inverse := SheafOfModules.RingedSite.RelativeDifferentials.inverseDerivation
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ
  let unit := SheafOfModules.RingedSite.RelativeDifferentials.unitDerivation
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ
  have hc : d.postcomp ((adj.homEquiv _ _) c).val = D := comparison_spec_aux f φ
  have hv : d'.postcomp v.val = inverse := differentialDesc_fac φ' inverse
  have hu : SheafOfModules.RelativeDerivation.InverseImage.pushforward
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ inverse = unit :=
    (SheafOfModules.RelativeDerivation.InverseImage.equiv
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ).apply_symm_apply unit
  constructor
  · show c ≫ v = 𝟙 _
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_id]
    apply differential_postcomp_injective φ
    calc
      _ = D.postcomp ((SheafOfModules.pushforward alpha).map v).val := by
        change (d.postcomp ((adj.homEquiv _ _) c).val).postcomp
          ((SheafOfModules.pushforward alpha).map v).val = _
        exact congrArg (fun E ↦ E.postcomp
          ((SheafOfModules.pushforward alpha).map v).val) hc
      _ = SheafOfModules.RelativeDerivation.InverseImage.pushforward
          (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
          (Opens.map f) φ (d'.postcomp v.val) := by
        ext U x
        rfl
      _ = unit := by rw [hv, hu]
  · show v ≫ c = 𝟙 _
    apply differential_postcomp_injective φ'
    apply (SheafOfModules.RelativeDerivation.InverseImage.equiv
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ).injective
    calc
      _ = (SheafOfModules.RelativeDerivation.InverseImage.pushforward
          (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
          (Opens.map f) φ (d'.postcomp v.val)).postcomp
            ((SheafOfModules.pushforward alpha).map c).val := by
        ext U x
        rfl
      _ = unit.postcomp ((SheafOfModules.pushforward alpha).map c).val := by
        rw [hv, hu]
      _ = d.postcomp ((adj.homEquiv _ _) c).val := by
        rw [Adjunction.homEquiv_unit]
        rfl
      _ = D := hc

/-- The inverse-image comparison on relative differentials is an isomorphism. -/
instance comparison_isIso (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIso (comparison f φ) :=
  ⟨⟨SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ, comparison_laws f φ⟩⟩

/-- The named inverse of the opens-site inverse-image relative-differentials comparison. -/
@[stacks 08RR "opens-site inverse-image differential comparison inverse"]
noncomputable abbrev comparisonInv (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ) ⟶
      (SheafOfModules.pullback (structureMap f O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The opens-site inverse-image differential comparison followed by its named inverse is the
identity. -/
@[simp, stacks 08RR "opens-site differential forward-inverse law"]
theorem comparison_hom_inv_id (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    comparison f φ ≫ comparisonInv f φ = 𝟙 _ :=
  (comparison_laws f φ).1

/-- The named inverse followed by the opens-site inverse-image differential comparison is the
identity. -/
@[simp, stacks 08RR "opens-site differential inverse-forward law"]
theorem comparison_inv_hom_id (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    comparisonInv f φ ≫ comparison f φ = 𝟙 _ :=
  (comparison_laws f φ).2

/-- Lemma 17.28.6 (08RR): inverse image commutes canonically with relative differentials. -/
@[stacks 08RR]
noncomputable abbrev iso (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback (structureMap f O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) ≅
      TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.comparisonIso
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The forward map of the inverse-image relative-differentials isomorphism is `comparison`. -/
@[stacks 08RR "inverse-image comparison isomorphism hom", simp]
theorem iso_hom (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (iso f φ).hom = comparison f φ := rfl

/-- The inverse projection of the opens-site inverse-image differential isomorphism is the named
inverse owner. -/
@[stacks 08RR "opens-site inverse-image differential isomorphism inverse", simp]
theorem iso_inv (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (iso f φ).inv = comparisonInv f φ := rfl

/-- The inverse-image comparison is characterized by the pulled universal derivation. -/
theorem comparison_spec (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ).IsPullbackDesc (comparison f φ) :=
  comparison_spec_aux f φ

/-- A morphism compatible with the pulled universal derivation is the canonical comparison. -/
theorem eq_comparison (f : Y ⟶ X) (φ : O₁ ⟶ O₂)
    {tau :
      (SheafOfModules.pullback (structureMap f O₂)).obj
          (TopCat.Sheaf.relativeDifferentials φ) ⟶
        TopCat.Sheaf.relativeDifferentials
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ)}
    (h_tau :
      (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ).IsPullbackDesc tau) :
    tau = comparison f φ := by
  apply ((SheafOfModules.pullbackPushforwardAdjunction
    (structureMap f O₂)).homEquiv _ _).injective
  apply differential_postcomp_injective φ
  exact h_tau.trans (comparison_spec f φ).symm

end TopCat.Sheaf.RelativeDifferentials.InverseImage
