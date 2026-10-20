/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}}

#check (positiveSectionsSystem :
  {X : Scheme.{u}} → X.IdealSheafData → X.Modules → SequentialInverseSystem (Type u))
#check (positiveSectionsSystem_obj :
  {X : Scheme.{u}} → (I : X.IdealSheafData) → (M : X.Modules) → (n : ℕ) →
    (positiveSectionsSystem I M).obj (op n) =
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        I.toSubobject M (n + 1)).sections)
#check (sectionsProjection :
  {X : Scheme.{u}} → (I : X.IdealSheafData) → (M : X.Modules) → (n : ℕ) →
    ((Functor.const ℕᵒᵖ).obj M.sections).obj (op n) ⟶
      (positiveSectionsSystem I M).obj (op n))
#check (sectionsProjection_naturality :
  {X : Scheme.{u}} → (I : X.IdealSheafData) → (M : X.Modules) → (n : ℕ) →
    ((Functor.const ℕᵒᵖ).obj M.sections).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ sectionsProjection I M n =
      sectionsProjection I M (n + 1) ≫
        (positiveSectionsSystem I M).map
          (homOfLE (Nat.le_add_right n 1)).op)
#check (sectionsCone :
  {X : Scheme.{u}} → (I : X.IdealSheafData) → (M : X.Modules) →
    Cone (positiveSectionsSystem I M))
#check (sectionsComparison :
  {X : Scheme.{u}} → (I : X.IdealSheafData) → (M : X.Modules) →
    M.sections → limit (positiveSectionsSystem I M))
#check (sectionsComparison_fac :
  {X : Scheme.{u}} → (I : X.IdealSheafData) → (M : X.Modules) → (n : ℕ) →
    ∀ s : M.sections,
      limit.π (positiveSectionsSystem I M) (op n) (sectionsComparison I M s) =
        sectionsProjection I M n s)
#check (finiteLocallyFree :
  (X : Scheme.{u}) → ObjectProperty (RingedSpace.Coh X.toRingedSpace))
#check (finiteLocallyFree_iff :
  (X : Scheme.{u}) → (E : RingedSpace.Coh X.toRingedSpace) →
    finiteLocallyFree X E ↔ SheafOfModules.IsFiniteLocallyFree E.obj)
#check (onFiniteLocallyFree :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    Functor (finiteLocallyFree X).FullSubcategory (CoherentFormalModules X I))
#check (onFiniteLocallyFree_obj :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (E : (finiteLocallyFree X).FullSubcategory) →
      (onFiniteLocallyFree I).obj E = (functor I).obj E.obj)
#check (quasiAffine_implies_hasAmple :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (hX : X.IsQuasiAffine) →
    (h_complete : Function.Bijective
      (sectionsComparison I (SheafOfModules.unit X.ringCatSheaf))) →
    ∃ L : X.Modules, Modules.isAmpleObject L ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀,
        Function.Bijective
          (sectionsComparison I (RingedSpace.TensorPower.sheaf L m)))
#check (hasAmple_implies_finiteLocallyFree :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) → (L : X.Modules) →
    (hL : Modules.isAmpleObject L) →
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (sectionsComparison I (RingedSpace.TensorPower.sheaf L m))) →
    ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj))
#check (finiteLocallyFree_implies_fullyFaithful :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (h_complete : ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj)) →
    Nonempty (onFiniteLocallyFree I).FullyFaithful)
#check (fullyFaithful_implies_finiteLocallyFree :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (h_fully_faithful : Nonempty (onFiniteLocallyFree I).FullyFaithful) →
    ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj))

end AlgebraicGeometry.Scheme.CoherentCompletion
