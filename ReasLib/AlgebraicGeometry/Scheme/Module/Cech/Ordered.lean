/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Augment
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Resolution
public import ReasLib.AlgebraicTopology.Cech.OrderedIndex

/-!
# Ordered module-valued Čech complexes

This module constructs the bounded ordered Čech complex of a module sheaf for a finite linearly
ordered family of opens of a scheme, together with its canonical augmentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleCech.Ordered

variable {X : Scheme.{u}} {ι : Type u} [Finite ι] [LinearOrder ι]

/-- The pushed-forward restriction belonging to a strictly increasing Čech index. -/
abbrev summand (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ)
    (σ : OrderedCechIndex ι p) : X.Modules :=
  AlgebraicGeometry.Scheme.openCoverModuleCechSummand 𝒰 ℱ p σ.toFun

/-- The finite biproduct of the summands indexed by strictly increasing tuples of length
`p + 1`. -/
abbrev term (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) : X.Modules :=
  ⨁ (fun σ : OrderedCechIndex ι p ↦ summand 𝒰 ℱ p σ)

/-- Deleting one entry from an ordered index induces the corresponding restriction morphism. -/
abbrev restriction (𝒰 : ι → X.Opens) (ℱ : X.Modules) {p : ℕ}
    (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    summand 𝒰 ℱ p (σ.delete j) ⟶ summand 𝒰 ℱ (p + 1) σ :=
  AlgebraicGeometry.Scheme.openCoverModuleCechRestriction 𝒰 ℱ σ.toFun j

/-- The alternating restriction differential between consecutive ordered Čech terms. -/
noncomputable def differential (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    term 𝒰 ℱ p ⟶ term 𝒰 ℱ (p + 1) :=
  biproduct.lift fun σ : OrderedCechIndex ι (p + 1) ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        (biproduct.π (fun τ : OrderedCechIndex ι p ↦ summand 𝒰 ℱ p τ) (σ.delete j) ≫
          restriction 𝒰 ℱ σ j)

/-- A target projection of the ordered differential is the signed sum of the restriction
components. -/
theorem differential_π (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ)
    (σ : OrderedCechIndex ι (p + 1)) :
    differential 𝒰 ℱ p ≫
        biproduct.π (fun τ : OrderedCechIndex ι (p + 1) ↦ summand 𝒰 ℱ (p + 1) τ) σ =
      ∑ j : Fin (p + 2),
        (-1 : ℤ) ^ (j : ℕ) •
          (biproduct.π (fun τ : OrderedCechIndex ι p ↦ summand 𝒰 ℱ p τ) (σ.delete j) ≫
            restriction 𝒰 ℱ σ j) := sorry

/-- Two consecutive ordered Čech differentials compose to zero. -/
theorem differential_comp (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    differential 𝒰 ℱ p ≫ differential 𝒰 ℱ (p + 1) = 0 := sorry

/-- The ordered module-valued Čech cochain complex of a finite family of opens. -/
noncomputable def complex (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex X.Modules ℕ :=
  CochainComplex.of (term 𝒰 ℱ) (differential 𝒰 ℱ) (differential_comp 𝒰 ℱ)

/-- The degree-`p` object of the ordered Čech complex is its finite biproduct term. -/
theorem complex_X (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    (complex 𝒰 ℱ).X p = term 𝒰 ℱ p := sorry

/-- The differential from degree `p` to degree `p + 1` is the alternating restriction map. -/
theorem complex_d (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    (complex 𝒰 ℱ).d p (p + 1) = differential 𝒰 ℱ p := sorry

/-- The canonical map from a module sheaf to the degree-zero ordered Čech term. -/
noncomputable def augmentationMap (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    ℱ ⟶ term 𝒰 ℱ 0 :=
  biproduct.lift fun σ : OrderedCechIndex ι 0 ↦
    (RingedSpace.OpenSubspace.Pushforward.adjunction X.toRingedSpace
      (TopCat.Presheaf.Cech.intersection 𝒰 σ.toFun)).unit.app ℱ

/-- Each projection of the augmentation map is the unit for restriction to the corresponding
open and pushforward. -/
theorem augmentationMap_π (𝒰 : ι → X.Opens) (ℱ : X.Modules)
    (σ : OrderedCechIndex ι 0) :
    augmentationMap 𝒰 ℱ ≫
        biproduct.π (fun τ : OrderedCechIndex ι 0 ↦ summand 𝒰 ℱ 0 τ) σ =
      (RingedSpace.OpenSubspace.Pushforward.adjunction X.toRingedSpace
        (TopCat.Presheaf.Cech.intersection 𝒰 σ.toFun)).unit.app ℱ := sorry

/-- The degree-zero augmentation is killed by the first ordered Čech differential. -/
theorem augmentationMap_comp_d (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    augmentationMap 𝒰 ℱ ≫ differential 𝒰 ℱ 0 = 0 := sorry

/-- The canonical augmentation from the module sheaf concentrated in degree zero to its ordered
Čech complex. -/
noncomputable def augmentation (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶ complex 𝒰 ℱ :=
  (CochainComplex.fromSingle₀Equiv (complex 𝒰 ℱ) ℱ).symm
    ⟨augmentationMap 𝒰 ℱ, augmentationMap_comp_d 𝒰 ℱ⟩

/-- The degree-zero component of the canonical augmentation is the explicit augmentation map. -/
theorem augmentation_f_zero (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    (augmentation 𝒰 ℱ).f 0 = augmentationMap 𝒰 ℱ := sorry

/-- The extended ordered Čech complex, with the original module sheaf in degree zero. -/
noncomputable def extended (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex X.Modules ℕ :=
  CochainComplex.fromSingle₀AsComplex (complex 𝒰 ℱ) ℱ (augmentation 𝒰 ℱ)

/-- Degree zero of the extended ordered Čech complex is the original module sheaf. -/
theorem extended_X_zero (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    (extended 𝒰 ℱ).X 0 = ℱ := sorry

/-- Degree `p + 1` of the extended ordered Čech complex is the ordered degree-`p` term. -/
theorem extended_X_succ (𝒰 : ι → X.Opens) (ℱ : X.Modules) (p : ℕ) :
    (extended 𝒰 ℱ).X (p + 1) = term 𝒰 ℱ p := sorry

end AlgebraicGeometry.Scheme.ModuleCech.Ordered

end
