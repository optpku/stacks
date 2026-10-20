/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.At.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Cohomology.Over
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of the canonical module `RHom`

This is the standard same-universe module-category facade for the generic K-injective cohomology
owner.  The generic owner remains carrier-polymorphic; this leaf provides short names for the
usual `ModuleCat.{u} A` presentation and exposes its universe-lifted comparison with shifted
derived morphisms.  No selected closed structure is part of this API.

@stack 0E1U
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.DerivedCategory.InternalHom.RHom

variable {A : Type u} [CommRing A]

namespace Cohomology

/-- 0E1U: The degree-`n` cohomology functor of canonical module `RHom`. -/
@[stacks 0E1U "degreewise cohomology of canonical module RHom"]
noncomputable abbrev functor (n : ℤ) [Has (A := A)] :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) ⥤
      ModuleCat.{u} A :=
  CochainComplex.Enriched.Over.RHom.Cohomology.functor
    (R := A) (C := ModuleCat.{u} A) n

/-- 0E1U: The universe-lifted shifted-Hom functor paired with canonical module `RHom` cohomology. -/
@[stacks 0E1U "universe-lifted shifted-Hom target for canonical module RHom"]
noncomputable abbrev shiftedFunctor (n : ℤ) :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) ⥤
      ModuleCat.{u + 1} A :=
  CochainComplex.Enriched.Over.RHom.Cohomology.shiftedFunctor
    (R := A) (C := ModuleCat.{u} A) n

/-- 0E1U: The universe-lifted cohomology functor used by the canonical shifted-Hom comparison. -/
@[stacks 0E1U "universe-lifted cohomology of canonical module RHom"]
noncomputable abbrev uliftFunctor (n : ℤ) [Has (A := A)] :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) ⥤
      ModuleCat.{u + 1} A :=
  CochainComplex.Enriched.Over.RHom.Cohomology.uliftFunctor
    (R := A) (C := ModuleCat.{u} A) n

section Grothendieck

variable [Has (A := A)]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{u} A)]

/-- 0E1U: The natural isomorphism from lifted canonical `RHom` cohomology to shifted derived Hom. -/
@[stacks 0E1U, stacks 0A64 "canonical module RHom cohomology comparison"]
noncomputable abbrev iso (n : ℤ) :
    uliftFunctor (A := A) n ≅ shiftedFunctor (A := A) n :=
  CochainComplex.Enriched.Over.RHom.Cohomology.iso
    (R := A) (C := ModuleCat.{u} A) n

/-- 0E1U: The canonical `A`-linear equivalence from cohomology of `RHom(K,L)` to shifted Hom. -/
@[stacks 0E1U, stacks 0A64 "canonical module RHom cohomology linear equivalence"]
noncomputable abbrev linearEquiv
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (functor (A := A) n).obj (Opposite.op K, L) ≃ₗ[A] ShiftedHom K L n :=
  CochainComplex.Enriched.Over.RHom.Cohomology.linearEquiv
    (R := A) (C := ModuleCat.{u} A) K L n

/-- 0E1U: Pointwise evaluation of the canonical module `RHom` cohomology equivalence. -/
@[simp, stacks 0E1U "canonical module RHom cohomology equivalence evaluation"]
theorem linearEquiv_apply
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (functor (A := A) n).obj (Opposite.op K, L)) :
    linearEquiv (A := A) K L n x =
      ((iso (A := A) n).hom.app (Opposite.op K, L) (ULift.up x)).down :=
  RHom.At.Cohomology.linearEquiv_apply (R := A) K L n x

/-- 0E1U: Naturality of the canonical module `RHom` cohomology comparison in both variables. -/
@[reassoc, stacks 0E1U "canonical module RHom cohomology comparison naturality"]
theorem iso_naturality (n : ℤ)
    {X Y : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A)}
    (f : X ⟶ Y) :
    (uliftFunctor (A := A) n).map f ≫ (iso (A := A) n).hom.app Y =
      (iso (A := A) n).hom.app X ≫ (shiftedFunctor (A := A) n).map f :=
  RHom.At.Cohomology.iso_naturality (R := A) n f

/-- The inverse canonical module `RHom` cohomology comparison is natural in both variables. -/
@[reassoc, stacks 0E1U "inverse canonical module RHom cohomology naturality"]
theorem iso_inv_naturality (n : ℤ)
    {X Y : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A)}
    (f : X ⟶ Y) :
    (shiftedFunctor (A := A) n).map f ≫ (iso (A := A) n).inv.app Y =
      (iso (A := A) n).inv.app X ≫ (uliftFunctor (A := A) n).map f :=
  RHom.At.Cohomology.iso_inv_naturality (R := A) n f

/-- The canonical module `RHom` cohomology comparison is natural in its source variable. -/
@[reassoc, stacks 0E1U, stacks 0A64 "canonical module RHom cohomology source naturality"]
theorem iso_natural_source
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ) :
    (uliftFunctor (A := A) n).map (f.op, 𝟙 L) ≫
        (iso (A := A) n).hom.app (Opposite.op K₂, L) =
      (iso (A := A) n).hom.app (Opposite.op K₁, L) ≫
        (shiftedFunctor (A := A) n).map (f.op, 𝟙 L) :=
  RHom.At.Cohomology.iso_natural_source (R := A) f n

/-- The canonical module `RHom` cohomology comparison is natural in its target variable. -/
@[reassoc, stacks 0E1U, stacks 0A64 "canonical module RHom cohomology target naturality"]
theorem iso_natural_target
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ) :
    (uliftFunctor (A := A) n).map (𝟙 (Opposite.op K), f) ≫
        (iso (A := A) n).hom.app (Opposite.op K, L₂) =
      (iso (A := A) n).hom.app (Opposite.op K, L₁) ≫
        (shiftedFunctor (A := A) n).map (𝟙 (Opposite.op K), f) :=
  RHom.At.Cohomology.iso_natural_target (R := A) K f n

/-- The inverse canonical module `RHom` cohomology comparison is natural in its source variable. -/
@[reassoc, stacks 0E1U "inverse canonical module RHom cohomology source naturality"]
theorem iso_inv_natural_source
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ) :
    (shiftedFunctor (A := A) n).map (f.op, 𝟙 L) ≫
        (iso (A := A) n).inv.app (Opposite.op K₂, L) =
      (iso (A := A) n).inv.app (Opposite.op K₁, L) ≫
        (uliftFunctor (A := A) n).map (f.op, 𝟙 L) :=
  RHom.At.Cohomology.iso_inv_natural_source (R := A) f n

/-- The inverse canonical module `RHom` cohomology comparison is natural in its target variable. -/
@[reassoc, stacks 0E1U "inverse canonical module RHom cohomology target naturality"]
theorem iso_inv_natural_target
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ) :
    (shiftedFunctor (A := A) n).map (𝟙 (Opposite.op K), f) ≫
        (iso (A := A) n).inv.app (Opposite.op K, L₂) =
      (iso (A := A) n).inv.app (Opposite.op K, L₁) ≫
        (uliftFunctor (A := A) n).map (𝟙 (Opposite.op K), f) :=
  RHom.At.Cohomology.iso_inv_natural_target (R := A) K f n

/-- 0E1U: The degree-zero cohomology of canonical module `RHom` as an ordinary derived morphism. -/
@[stacks 0E1U "degree-zero canonical module RHom cohomology linear equivalence"]
noncomputable def linearEquiv_zero
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (functor (A := A) (0 : ℤ)).obj (Opposite.op K, L) ≃ₗ[A] (K ⟶ L) :=
  (linearEquiv (A := A) K L (0 : ℤ)).trans
    (ShiftedHom.zeroLinearEquiv A K L)

/-- 0E1U: Evaluation of the degree-zero canonical module `RHom` cohomology equivalence. -/
@[simp, stacks 0E1U "degree-zero canonical module RHom cohomology evaluation"]
theorem linearEquiv_zero_apply
    (K L : DerivedCategory (ModuleCat.{u} A))
    (x : (functor (A := A) (0 : ℤ)).obj (Opposite.op K, L)) :
    linearEquiv_zero (A := A) K L x =
      ShiftedHom.zeroLinearEquiv A K L
        (linearEquiv (A := A) K L (0 : ℤ) x) :=
  RHom.At.Cohomology.linearEquiv_zero_apply (R := A) K L x

/-- The canonical cohomology equivalence carries source maps to precomposition in shifted Hom. -/
@[simp, stacks 0E1U "canonical module RHom cohomology source map"]
theorem linearEquiv_natural_source
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (functor (A := A) n).obj (Opposite.op K₁, L)) :
    linearEquiv (A := A) K₂ L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (RHom.map (A := A) f (𝟙 L))).hom x) =
      f ≫ linearEquiv (A := A) K₁ L n x :=
  RHom.At.Cohomology.linearEquiv_natural_source (R := A) f n x

/-- The canonical cohomology equivalence carries target maps to postcomposition in shifted Hom. -/
@[simp, stacks 0E1U "canonical module RHom cohomology target map"]
theorem linearEquiv_natural_target
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ)
    (x : (functor (A := A) n).obj (Opposite.op K, L₁)) :
    linearEquiv (A := A) K L₂ n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (RHom.map (A := A) (𝟙 K) f)).hom x) =
      linearEquiv (A := A) K L₁ n x ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).map f :=
  RHom.At.Cohomology.linearEquiv_natural_target (R := A) K f n x

/-- The canonical degree-zero cohomology equivalence carries source maps to composition. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom source map"]
theorem linearEquiv_zero_natural_source
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁)
    (x : (functor (A := A) (0 : ℤ)).obj (Opposite.op K₁, L)) :
    linearEquiv_zero (A := A) K₂ L
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (RHom.map (A := A) f (𝟙 L))).hom x) =
      f ≫ linearEquiv_zero (A := A) K₁ L x :=
  RHom.At.Cohomology.linearEquiv_zero_natural_source (R := A) f x

/-- The canonical degree-zero cohomology equivalence carries target maps to composition. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom target map"]
theorem linearEquiv_zero_natural_target
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    (x : (functor (A := A) (0 : ℤ)).obj (Opposite.op K, L₁)) :
    linearEquiv_zero (A := A) K L₂
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (RHom.map (A := A) (𝟙 K) f)).hom x) =
      linearEquiv_zero (A := A) K L₁ x ≫ f :=
  RHom.At.Cohomology.linearEquiv_zero_natural_target (R := A) K f x

/-- 0E1U: The canonical cohomology comparison from shifted derived morphisms. -/
@[stacks 0E1U "canonical module RHom cohomology comparison"]
noncomputable def comparison
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ShiftedHom K L n →ₗ[A] (functor (A := A) n).obj (Opposite.op K, L) :=
  (linearEquiv (A := A) K L n).symm.toLinearMap

/-- Evaluation of the canonical cohomology comparison. -/
@[simp, stacks 0E1U "canonical module RHom cohomology comparison evaluation"]
theorem comparison_apply
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : ShiftedHom K L n) :
    comparison (A := A) K L n x = (linearEquiv (A := A) K L n).symm x :=
  RHom.At.Cohomology.comparison_apply (R := A) K L n x

/-- Applying the canonical cohomology equivalence after comparison recovers the shifted morphism. -/
@[simp, stacks 0E1U "canonical module RHom cohomology comparison left inverse"]
theorem linearEquiv_comparison
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : ShiftedHom K L n) :
    linearEquiv (A := A) K L n (comparison (A := A) K L n x) = x :=
  RHom.At.Cohomology.linearEquiv_comparison (R := A) K L n x

/-- Applying the canonical comparison after the cohomology equivalence recovers the class. -/
@[simp, stacks 0E1U "canonical module RHom cohomology comparison right inverse"]
theorem comparison_linearEquiv
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (functor (A := A) n).obj (Opposite.op K, L)) :
    comparison (A := A) K L n (linearEquiv (A := A) K L n x) = x :=
  RHom.At.Cohomology.comparison_linearEquiv (R := A) K L n x

/-- The canonical comparison carries source composition to the cohomology map induced by
canonical `RHom` precomposition. -/
@[simp, stacks 0E1U "canonical module RHom cohomology comparison source naturality"]
theorem comparison_natural_source
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : ShiftedHom K₁ L n) :
    comparison (A := A) K₂ L n (f ≫ x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (RHom.map (A := A) f (𝟙 L))).hom
          (comparison (A := A) K₁ L n x) :=
  RHom.At.Cohomology.comparison_natural_source (R := A) f n x

/-- The canonical comparison carries target composition to the cohomology map induced by the
canonical `RHom` target map. -/
@[simp, stacks 0E1U "canonical module RHom cohomology comparison target naturality"]
theorem comparison_natural_target
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ)
    (x : ShiftedHom K L₁ n) :
    comparison (A := A) K L₂ n
        (x ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).map f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (RHom.map (A := A) (𝟙 K) f)).hom
          (comparison (A := A) K L₁ n x) :=
  RHom.At.Cohomology.comparison_natural_target (R := A) K f n x

/-- 0E1U: The canonical degree-zero comparison from ordinary derived morphisms. -/
@[stacks 0E1U "canonical degree-zero module RHom comparison"]
noncomputable def comparisonZero
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (K ⟶ L) →ₗ[A] (functor (A := A) (0 : ℤ)).obj (Opposite.op K, L) :=
  (linearEquiv_zero (A := A) K L).symm.toLinearMap

/-- Evaluation of the canonical degree-zero comparison. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom comparison evaluation"]
theorem comparisonZero_apply
    (K L : DerivedCategory (ModuleCat.{u} A)) (f : K ⟶ L) :
    comparisonZero (A := A) K L f = (linearEquiv_zero (A := A) K L).symm f :=
  RHom.At.Cohomology.comparisonZero_apply (R := A) K L f

/-- Applying the canonical degree-zero equivalence after comparison recovers the morphism. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom comparison left inverse"]
theorem linearEquiv_zero_comparisonZero
    (K L : DerivedCategory (ModuleCat.{u} A)) (f : K ⟶ L) :
    linearEquiv_zero (A := A) K L (comparisonZero (A := A) K L f) = f :=
  RHom.At.Cohomology.linearEquiv_zero_comparisonZero (R := A) K L f

/-- Applying the canonical degree-zero comparison after equivalence recovers the class. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom comparison right inverse"]
theorem comparisonZero_linearEquiv_zero
    (K L : DerivedCategory (ModuleCat.{u} A))
    (x : (functor (A := A) (0 : ℤ)).obj (Opposite.op K, L)) :
    comparisonZero (A := A) K L (linearEquiv_zero (A := A) K L x) = x :=
  RHom.At.Cohomology.comparisonZero_linearEquiv_zero (R := A) K L x

/-- The degree-zero canonical comparison carries source composition to canonical `RHom`
cohomology. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom comparison source naturality"]
theorem comparisonZero_natural_source
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (g' : K₁ ⟶ L) :
    comparisonZero (A := A) K₂ L (f ≫ g') =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (0 : ℤ)).map
        (RHom.map (A := A) f (𝟙 L))).hom
          (comparisonZero (A := A) K₁ L g') :=
  RHom.At.Cohomology.comparisonZero_natural_source (R := A) f g'

/-- The degree-zero canonical comparison carries target composition to canonical `RHom`
cohomology. -/
@[simp, stacks 0E1U "canonical degree-zero module RHom comparison target naturality"]
theorem comparisonZero_natural_target
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (g' : K ⟶ L₁) :
    comparisonZero (A := A) K L₂ (g' ≫ f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (0 : ℤ)).map
        (RHom.map (A := A) (𝟙 K) f)).hom
          (comparisonZero (A := A) K L₁ g') :=
  RHom.At.Cohomology.comparisonZero_natural_target (R := A) K f g'

end Grothendieck

end Cohomology

end CategoryTheory.DerivedCategory.InternalHom.RHom

/-! The aligned coherent facade is a specialization of the carrier-polymorphic owner above. -/

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BifunctorComparison.Cohomology

open CategoryTheory
open CategoryTheory.MonoidalClosed

variable {A : Type u} [CommRing A]
variable [RHom.Has (A := A)]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{u} A)]

/-- 0E1U: The aligned cohomology bifunctor of a coherent selected internal Hom. -/
@[stacks 0E1U "same-universe coherent selected internal-Hom cohomology bifunctor"]
noncomputable abbrev functor
    (M : RHom.BifunctorComparison (A := A)) (n : ℤ) :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) ⥤
      ModuleCat.{u + 1, u} A :=
  RHom.At.BifunctorComparison.Cohomology.functor (R := A) M n

/-- 0E1U: The aligned natural isomorphism from selected internal-Hom cohomology to shifted Hom. -/
@[stacks 0E1U "same-universe coherent selected cohomology comparison"]
noncomputable abbrev iso
    (M : RHom.BifunctorComparison (A := A)) (n : ℤ) :
    functor M n ≅ RHom.Cohomology.shiftedFunctor (A := A) n :=
  RHom.At.BifunctorComparison.Cohomology.iso (R := A) M n

/-- The forward component of the aligned selected cohomology comparison. -/
@[stacks 0E1U "aligned selected cohomology comparison component"]
theorem iso_hom_app
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (iso M n).hom.app (Opposite.op K, L) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙
        ModuleCat.uliftFunctor.{u + 1, u} A).map (M.objIso K L).inv) ≫
        (RHom.Cohomology.iso (A := A) n).hom.app (Opposite.op K, L) :=
  RHom.At.BifunctorComparison.Cohomology.iso_hom_app (R := A) M K L n

/-- The inverse component of the aligned selected cohomology comparison. -/
@[stacks 0E1U "inverse aligned selected cohomology comparison component"]
theorem iso_inv_app
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (iso M n).inv.app (Opposite.op K, L) =
      (RHom.Cohomology.iso (A := A) n).inv.app (Opposite.op K, L) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙
          ModuleCat.uliftFunctor.{u + 1, u} A).map (M.objIso K L).hom) :=
  RHom.At.BifunctorComparison.Cohomology.iso_inv_app (R := A) M K L n

/-- 0E1U: Naturality of the aligned selected cohomology comparison in both variables. -/
@[reassoc, stacks 0E1U "aligned selected cohomology naturality"]
theorem iso_naturality
    (M : RHom.BifunctorComparison (A := A)) (n : ℤ)
    {X Y : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A)}
    (f : X ⟶ Y) :
    (functor M n).map f ≫ (iso M n).hom.app Y =
      (iso M n).hom.app X ≫ (RHom.Cohomology.shiftedFunctor (A := A) n).map f :=
  RHom.At.BifunctorComparison.Cohomology.iso_naturality (R := A) M n f

/-- The inverse aligned selected cohomology comparison is natural in both variables. -/
@[reassoc, stacks 0E1U "inverse aligned selected cohomology naturality"]
theorem iso_inv_naturality
    (M : RHom.BifunctorComparison (A := A)) (n : ℤ)
    {X Y : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A)}
    (f : X ⟶ Y) :
    (RHom.Cohomology.shiftedFunctor (A := A) n).map f ≫ (iso M n).inv.app Y =
      (iso M n).inv.app X ≫ (functor M n).map f :=
  RHom.At.BifunctorComparison.Cohomology.iso_inv_naturality (R := A) M n f

/-- The aligned selected cohomology comparison is natural in the source variable. -/
@[reassoc, stacks 0E1U "aligned selected cohomology source naturality"]
theorem iso_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ) :
    (functor M n).map (f.op, 𝟙 L) ≫ (iso M n).hom.app (Opposite.op K₂, L) =
      (iso M n).hom.app (Opposite.op K₁, L) ≫
        (RHom.Cohomology.shiftedFunctor (A := A) n).map (f.op, 𝟙 L) :=
  RHom.At.BifunctorComparison.Cohomology.iso_natural_source (R := A) M n f

/-- The aligned selected cohomology comparison is natural in the target variable. -/
@[reassoc, stacks 0E1U "aligned selected cohomology target naturality"]
theorem iso_natural_target
    (M : RHom.BifunctorComparison (A := A)) (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ) :
    (functor M n).map (𝟙 (Opposite.op K), f) ≫ (iso M n).hom.app (Opposite.op K, L₂) =
      (iso M n).hom.app (Opposite.op K, L₁) ≫
        (RHom.Cohomology.shiftedFunctor (A := A) n).map (𝟙 (Opposite.op K), f) :=
  RHom.At.BifunctorComparison.Cohomology.iso_natural_target (R := A) M n K f

/-- The inverse aligned selected cohomology comparison is natural in the source variable. -/
@[reassoc, stacks 0E1U "inverse aligned selected cohomology source naturality"]
theorem iso_inv_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ) :
    (RHom.Cohomology.shiftedFunctor (A := A) n).map (f.op, 𝟙 L) ≫
        (iso M n).inv.app (Opposite.op K₂, L) =
      (iso M n).inv.app (Opposite.op K₁, L) ≫ (functor M n).map (f.op, 𝟙 L) :=
  RHom.At.BifunctorComparison.Cohomology.iso_inv_natural_source (R := A) M n f

/-- The inverse aligned selected cohomology comparison is natural in the target variable. -/
@[reassoc, stacks 0E1U "inverse aligned selected cohomology target naturality"]
theorem iso_inv_natural_target
    (M : RHom.BifunctorComparison (A := A)) (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ) :
    (RHom.Cohomology.shiftedFunctor (A := A) n).map (𝟙 (Opposite.op K), f) ≫
        (iso M n).inv.app (Opposite.op K, L₂) =
      (iso M n).inv.app (Opposite.op K, L₁) ≫ (functor M n).map (𝟙 (Opposite.op K), f) :=
  RHom.At.BifunctorComparison.Cohomology.iso_inv_natural_target (R := A) M n K f

/-- The aligned selected cohomology equivalence obtained from the coherent comparison. -/
@[stacks 0E1U "aligned selected cohomology equivalence"]
noncomputable def linearEquiv
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((ihomOf M.closed K).obj L) ≃ₗ[A] ShiftedHom K L n :=
  (ULift.moduleEquiv (R := A)
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((ihomOf M.closed K).obj L))).symm.trans <|
    ((iso M n).app (Opposite.op K, L)).toLinearEquiv.trans <|
      ULift.moduleEquiv (R := A) (M := ShiftedHom K L n)

/-- The aligned selected cohomology equivalence evaluated on a class. -/
@[simp, stacks 0E1U "aligned selected cohomology equivalence evaluation"]
theorem linearEquiv_apply
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((ihomOf M.closed K).obj L)) :
    linearEquiv M K L n x =
      ((iso M n).hom.app (Opposite.op K, L) (ULift.up x)).down :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_apply (R := A) M K L n x

/-- The aligned selected cohomology equivalence after transport to canonical `RHom`. -/
@[simp, stacks 0E1U "aligned selected cohomology canonical transport"]
theorem linearEquiv_eq_canonical
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((ihomOf M.closed K).obj L)) :
    linearEquiv M K L n x =
      RHom.Cohomology.linearEquiv (A := A) K L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (M.objIso K L).inv).hom x) :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_eq_canonical (R := A) M K L n x

/-- The aligned selected cohomology equivalence is natural in its source variable. -/
@[simp, stacks 0E1U "aligned selected cohomology source map"]
theorem linearEquiv_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((ihomOf M.closed K₁).obj L)) :
    linearEquiv M K₂ L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((preOf M.closed f).app L)).hom x) =
      f ≫ linearEquiv M K₁ L n x :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_natural_source (R := A) M f n x

/-- The aligned selected cohomology equivalence is natural in its target variable. -/
@[simp, stacks 0E1U "aligned selected cohomology target map"]
theorem linearEquiv_natural_target
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((ihomOf M.closed K).obj L₁)) :
    linearEquiv M K L₂ n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((ihomOf M.closed K).map f)).hom x) =
      linearEquiv M K L₁ n x ≫ (shiftFunctor
        (DerivedCategory (ModuleCat.{u} A)) n).map f :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_natural_target (R := A) M K f n x

/-- The aligned inverse comparison from shifted Hom to selected cohomology. -/
@[stacks 0E1U "aligned inverse selected-cohomology comparison"]
noncomputable def comparison
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ShiftedHom K L n →ₗ[A]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((ihomOf M.closed K).obj L) :=
  (linearEquiv M K L n).symm.toLinearMap

/-- Evaluation of the aligned inverse cohomology comparison. -/
@[simp, stacks 0E1U "aligned selected cohomology comparison evaluation"]
theorem comparison_apply
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : ShiftedHom K L n) :
    comparison M K L n x = (linearEquiv M K L n).symm x :=
  RHom.At.BifunctorComparison.Cohomology.comparison_apply (R := A) M K L n x

/-- The aligned selected comparison after transport to canonical `RHom` cohomology. -/
@[simp, stacks 0E1U "aligned selected cohomology canonical comparison"]
theorem comparison_eq_canonical
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : ShiftedHom K L n) :
    comparison M K L n x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (M.objIso K L).hom).hom
          (RHom.Cohomology.comparison (A := A) K L n x) :=
  RHom.At.BifunctorComparison.Cohomology.comparison_eq_canonical (R := A) M K L n x

/-- Applying the aligned selected equivalence after comparison recovers the shifted morphism. -/
@[simp, stacks 0E1U "aligned selected cohomology comparison left inverse"]
theorem linearEquiv_comparison
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (x : ShiftedHom K L n) :
    linearEquiv M K L n (comparison M K L n x) = x :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_comparison (R := A) M K L n x

/-- Applying the aligned comparison after the selected equivalence recovers the class. -/
@[simp, stacks 0E1U "aligned selected cohomology comparison right inverse"]
theorem comparison_linearEquiv
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((ihomOf M.closed K).obj L)) :
    comparison M K L n (linearEquiv M K L n x) = x :=
  RHom.At.BifunctorComparison.Cohomology.comparison_linearEquiv (R := A) M K L n x

/-- The aligned comparison carries source composition to selected precomposition on cohomology. -/
@[simp, stacks 0E1U "aligned selected cohomology comparison source naturality"]
theorem comparison_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)}
    (f : K₂ ⟶ K₁) (n : ℤ) (x : ShiftedHom K₁ L n) :
    comparison M K₂ L n (f ≫ x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((preOf M.closed f).app L)).hom (comparison M K₁ L n x) :=
  RHom.At.BifunctorComparison.Cohomology.comparison_natural_source (R := A) M f n x

/-- The aligned comparison carries target composition to selected target maps on cohomology. -/
@[simp, stacks 0E1U "aligned selected cohomology comparison target naturality"]
theorem comparison_natural_target
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)}
    (f : L₁ ⟶ L₂) (n : ℤ) (x : ShiftedHom K L₁ n) :
    comparison M K L₂ n (x ≫ (shiftFunctor
      (DerivedCategory (ModuleCat.{u} A)) n).map f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((ihomOf M.closed K).map f)).hom (comparison M K L₁ n x) :=
  RHom.At.BifunctorComparison.Cohomology.comparison_natural_target (R := A) M K f n x

/-- 0E1U: Degree-zero cohomology of an aligned selected internal Hom is ordinary derived Hom. -/
@[stacks 0E1U "aligned selected degree-zero cohomology equivalence"]
noncomputable def linearEquiv_zero
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((ihomOf M.closed K).obj L) ≃ₗ[A] (K ⟶ L) :=
  (linearEquiv M K L 0).trans (ShiftedHom.zeroLinearEquiv A K L)

/-- Evaluation of the aligned degree-zero selected equivalence. -/
@[simp, stacks 0E1U "aligned selected degree-zero cohomology evaluation"]
theorem linearEquiv_zero_apply
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((ihomOf M.closed K).obj L)) :
    linearEquiv_zero M K L x =
      ShiftedHom.zeroLinearEquiv A K L (linearEquiv M K L 0 x) :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_zero_apply (R := A) M K L x

/-- The aligned degree-zero selected equivalence after transport to canonical `RHom`. -/
@[simp, stacks 0E1U "aligned selected degree-zero canonical transport"]
theorem linearEquiv_zero_eq_canonical
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((ihomOf M.closed K).obj L)) :
    linearEquiv_zero M K L x =
      RHom.Cohomology.linearEquiv_zero (A := A) K L
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (M.objIso K L).inv).hom x) :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_zero_eq_canonical (R := A) M K L x

/-- The aligned degree-zero selected equivalence is natural in the source variable. -/
@[simp, stacks 0E1U "aligned selected degree-zero source naturality"]
theorem linearEquiv_zero_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((ihomOf M.closed K₁).obj L)) :
    linearEquiv_zero M K₂ L
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((preOf M.closed f).app L)).hom x) =
      f ≫ linearEquiv_zero M K₁ L x :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_zero_natural_source (R := A) M f x

/-- The aligned degree-zero selected equivalence is natural in the target variable. -/
@[simp, stacks 0E1U "aligned selected degree-zero target naturality"]
theorem linearEquiv_zero_natural_target
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((ihomOf M.closed K).obj L₁)) :
    linearEquiv_zero M K L₂
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((ihomOf M.closed K).map f)).hom x) =
      linearEquiv_zero M K L₁ x ≫ f :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_zero_natural_target (R := A) M K f x

/-- The aligned degree-zero comparison from ordinary derived Hom to selected cohomology. -/
@[stacks 0E1U "aligned selected degree-zero comparison"]
noncomputable def comparisonZero
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (K ⟶ L) →ₗ[A]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((ihomOf M.closed K).obj L) :=
  (linearEquiv_zero M K L).symm.toLinearMap

/-- Evaluation of the aligned degree-zero comparison. -/
@[simp, stacks 0E1U "aligned selected degree-zero comparison evaluation"]
theorem comparisonZero_apply
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (f : K ⟶ L) :
    comparisonZero M K L f = (linearEquiv_zero M K L).symm f :=
  RHom.At.BifunctorComparison.Cohomology.comparisonZero_apply (R := A) M K L f

/-- The aligned degree-zero selected comparison after transport to canonical `RHom`. -/
@[simp, stacks 0E1U "aligned selected degree-zero canonical comparison"]
theorem comparisonZero_eq_canonical
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (f : K ⟶ L) :
    comparisonZero M K L f =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (M.objIso K L).hom).hom
          (RHom.Cohomology.comparisonZero (A := A) K L f) :=
  RHom.At.BifunctorComparison.Cohomology.comparisonZero_eq_canonical (R := A) M K L f

/-- Applying the aligned degree-zero equivalence after comparison recovers the morphism. -/
@[simp, stacks 0E1U "aligned selected degree-zero comparison left inverse"]
theorem linearEquiv_zero_comparisonZero
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (f : K ⟶ L) :
    linearEquiv_zero M K L (comparisonZero M K L f) = f :=
  RHom.At.BifunctorComparison.Cohomology.linearEquiv_zero_comparisonZero (R := A) M K L f

/-- Applying the aligned degree-zero comparison after equivalence recovers the class. -/
@[simp, stacks 0E1U "aligned selected degree-zero comparison right inverse"]
theorem comparisonZero_linearEquiv_zero
    (M : RHom.BifunctorComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((ihomOf M.closed K).obj L)) :
    comparisonZero M K L (linearEquiv_zero M K L x) = x :=
  RHom.At.BifunctorComparison.Cohomology.comparisonZero_linearEquiv_zero (R := A) M K L x

/-- The aligned degree-zero comparison carries source composition to selected precomposition. -/
@[simp, stacks 0E1U "aligned selected degree-zero comparison source naturality"]
theorem comparisonZero_natural_source
    (M : RHom.BifunctorComparison (A := A))
    {K₁ K₂ L : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁) (g' : K₁ ⟶ L) :
    comparisonZero M K₂ L (f ≫ g') =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((preOf M.closed f).app L)).hom (comparisonZero M K₁ L g') :=
  RHom.At.BifunctorComparison.Cohomology.comparisonZero_natural_source (R := A) M f g'

/-- The aligned degree-zero comparison carries target composition to selected target maps. -/
@[simp, stacks 0E1U "aligned selected degree-zero comparison target naturality"]
theorem comparisonZero_natural_target
    (M : RHom.BifunctorComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (g' : K ⟶ L₁) :
    comparisonZero M K L₂ (g' ≫ f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((ihomOf M.closed K).map f)).hom (comparisonZero M K L₁ g') :=
  RHom.At.BifunctorComparison.Cohomology.comparisonZero_natural_target (R := A) M K f g'

end CategoryTheory.DerivedCategory.InternalHom.RHom.BifunctorComparison.Cohomology

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.At.Cohomology

open CategoryTheory

variable {A : Type u} [CommRing A]
variable [RHom.At.Has.{u, u} (R := A)]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{u} A)]

/-- The carrier-polymorphic canonical cohomology comparison specializes to the aligned facade. -/
theorem linearEquiv_eq_aligned
    (K L : RHom.At.Derived.{u, u} (R := A)) (n : ℤ) :
    RHom.At.Cohomology.linearEquiv (R := A) K L n =
      RHom.Cohomology.linearEquiv (A := A) K L n := rfl

/-- The carrier-polymorphic canonical comparison specializes to the aligned facade. -/
theorem comparison_eq_aligned
    (K L : RHom.At.Derived.{u, u} (R := A)) (n : ℤ) :
    RHom.At.Cohomology.comparison (R := A) K L n =
      RHom.Cohomology.comparison (A := A) K L n := rfl

/-- The carrier-polymorphic degree-zero equivalence specializes to the aligned facade. -/
theorem linearEquiv_zero_eq_aligned
    (K L : RHom.At.Derived.{u, u} (R := A)) :
    RHom.At.Cohomology.linearEquiv_zero (R := A) K L =
      RHom.Cohomology.linearEquiv_zero (A := A) K L := rfl

/-- The carrier-polymorphic degree-zero comparison specializes to the aligned facade. -/
theorem comparisonZero_eq_aligned
    (K L : RHom.At.Derived.{u, u} (R := A)) :
    RHom.At.Cohomology.comparisonZero (R := A) K L =
      RHom.Cohomology.comparisonZero (A := A) K L := rfl

end CategoryTheory.DerivedCategory.InternalHom.RHom.At.Cohomology

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.At.BifunctorComparison.Cohomology

universe u g

open CategoryTheory

variable {A : Type u} [CommRing A]
variable [RHom.At.Has.{u, u} (R := A)]
variable [MonoidalCategory (RHom.At.Derived.{u, u} (R := A))]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{u} A)]

/-- The carrier-polymorphic coherent cohomology comparison specializes to the aligned facade. -/
theorem iso_eq_aligned
    (M : RHom.BifunctorComparison (A := A)) (n : ℤ) :
    RHom.At.BifunctorComparison.Cohomology.iso (R := A) M n =
      RHom.BifunctorComparison.Cohomology.iso M n := rfl

/-- The carrier-polymorphic coherent cohomology equivalence specializes to the aligned facade. -/
theorem linearEquiv_eq_aligned
    (M : RHom.BifunctorComparison (A := A))
    (K L : RHom.At.Derived.{u, u} (R := A)) (n : ℤ) :
    RHom.At.BifunctorComparison.Cohomology.linearEquiv (R := A) M K L n =
      RHom.BifunctorComparison.Cohomology.linearEquiv M K L n := rfl

/-- The carrier-polymorphic coherent comparison specializes to the aligned facade. -/
theorem comparison_eq_aligned
    (M : RHom.BifunctorComparison (A := A))
    (K L : RHom.At.Derived.{u, u} (R := A)) (n : ℤ) :
    RHom.At.BifunctorComparison.Cohomology.comparison (R := A) M K L n =
      RHom.BifunctorComparison.Cohomology.comparison M K L n := rfl

/-- The carrier-polymorphic coherent degree-zero equivalence specializes to the aligned facade. -/
theorem linearEquiv_zero_eq_aligned
    (M : RHom.BifunctorComparison (A := A))
    (K L : RHom.At.Derived.{u, u} (R := A)) :
    RHom.At.BifunctorComparison.Cohomology.linearEquiv_zero (R := A) M K L =
      RHom.BifunctorComparison.Cohomology.linearEquiv_zero M K L := rfl

/-- The carrier-polymorphic coherent degree-zero comparison specializes to the aligned facade. -/
theorem comparisonZero_eq_aligned
    (M : RHom.BifunctorComparison (A := A))
    (K L : RHom.At.Derived.{u, u} (R := A)) :
    RHom.At.BifunctorComparison.Cohomology.comparisonZero (R := A) M K L =
      RHom.BifunctorComparison.Cohomology.comparisonZero M K L := rfl

end CategoryTheory.DerivedCategory.InternalHom.RHom.At.BifunctorComparison.Cohomology
