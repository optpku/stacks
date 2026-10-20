/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Cohomology
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Preadditive.HomCongr
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of module-valued and standard Hom complexes

For an `R`-linear category, the enriched Hom complex is naturally `ModuleCat R`-valued.
Forgetting its scalar action gives Mathlib's standard `AddCommGrpCat`-valued `HomComplex`.
This file owns that chain-level identification, its induced homology comparison, and the
canonical linear equivalence with shifted morphisms in the homotopy category.
@stack 0GWQ
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory ComplexShape HomotopyCategory
open CategoryTheory.CochainComplex

namespace CochainComplex.HomComplex.Module

variable (R : Type w) [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The module-valued Hom complex after forgetting its `R`-module structure degreewise. -/
@[stacks 0A8H "forgotten module-valued Hom complex"]
abbrev forgetComplex (M N : CochainComplex C ℤ) :
    CochainComplex AddCommGrpCat ℤ :=
  ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex (up ℤ)).obj
    (moduleComplex R M N)

/-- The map of enriched Hom complexes after forgetting the scalar action. -/
@[stacks 0GWQ "functoriality of the forgotten module-valued Hom complex"]
def forgetMap {M₁ M₂ N₁ N₂ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) :
    forgetComplex R M₁ N₁ ⟶ forgetComplex R M₂ N₂ :=
  ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex (up ℤ)).map
    (map R f g)

/-- The forgotten enriched Hom-complex map preserves identities. -/
@[simp]
theorem forgetMap_id (M N : CochainComplex C ℤ) :
    forgetMap R (𝟙 M) (𝟙 N) = 𝟙 (forgetComplex R M N) := sorry

/-- The forgotten enriched Hom-complex map preserves composition with the source variance
reversed. -/
theorem forgetMap_comp
    {M₁ M₂ M₃ N₁ N₂ N₃ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (f' : M₃ ⟶ M₂) (g : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃) :
    forgetMap R (f' ≫ f) (g ≫ g') =
      forgetMap R f g ≫ forgetMap R f' g' := sorry

/-- Identity components commute with the differentials of the forgotten enriched Hom complex
and Mathlib's standard Hom complex. -/
theorem complexIso_comm (M N : CochainComplex C ℤ) :
    ∀ i j, (up ℤ).Rel i j →
      (𝟙 ((forgetComplex R M N).X i)) ≫ (HomComplex M N).d i j =
        (forgetComplex R M N).d i j ≫ 𝟙 ((HomComplex M N).X j) := sorry

/-- Forgetting the scalar action on the module-valued Hom complex canonically recovers
Mathlib's standard Hom complex. -/
@[stacks 0A8H "module-valued Hom complex agrees with Mathlib HomComplex"]
noncomputable def complexIso (M N : CochainComplex C ℤ) :
    forgetComplex R M N ≅ HomComplex M N :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (complexIso_comm R M N)

/-- The forward chain-level comparison is the identity in every degree. -/
@[simp]
theorem complexIso_hom_f (M N : CochainComplex C ℤ) (n : ℤ) :
    (complexIso R M N).hom.f n = 𝟙 _ := sorry

/-- The inverse chain-level comparison is the identity in every degree. -/
@[simp]
theorem complexIso_inv_f (M N : CochainComplex C ℤ) (n : ℤ) :
    (complexIso R M N).inv.f n = 𝟙 _ := sorry

/-- The chain-level comparison is contravariantly natural in the source and covariantly
natural in the target. -/
@[stacks 0A8H "naturality of the module-valued Hom-complex comparison"]
theorem complexIso_naturality
    {M₁ M₂ N₁ N₂ : CochainComplex C ℤ} (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) :
    forgetMap R f g ≫ (complexIso R M₂ N₂).hom =
      (complexIso R M₁ N₁).hom ≫ homComplexPrecomp f ≫ homComplexPostcomp g := sorry

/-- The canonical comparison from enriched Hom-complex homology to Mathlib Hom-complex
homology. -/
@[stacks 0A8L "module-valued and standard Hom-complex cohomology comparison"]
noncomputable def homologyIso (M N : CochainComplex C ℤ) (n : ℤ) :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj
        ((moduleComplex R M N).homology n) ≅
      (HomComplex M N).homology n :=
  ((moduleComplex R M N).mapHomologyIso
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) n).symm ≪≫
    HomologicalComplex.homologyMapIso (complexIso R M N) n

/-- The additive equivalence underlying the comparison of the two Hom-complex homology
objects. -/
@[stacks 0A8L "module-valued and standard Hom-complex cohomology equivalence"]
noncomputable def homologyAddEquiv (M N : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplex R M N).homology n ≃+
      (HomComplex M N).homology n :=
  (homologyIso R M N n).addCommGroupIsoToAddEquiv

/-- Module-valued Hom-complex cohomology is canonically additively equivalent to morphisms
into a shifted complex in the homotopy category. -/
@[stacks 0A8L "module-valued Hom-complex cohomology as homotopy Hom"]
noncomputable def homologyHomAddEquiv (M N : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplex R M N).homology n ≃+
      ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (N⟦n⟧)) :=
  (homologyAddEquiv R M N n).trans
    (CochainComplex.HomComplex.homologyHomAddEquiv M N n)

/-- Module-valued Hom-complex cohomology is canonically linearly equivalent to shifted
morphisms in the homotopy category. -/
@[stacks 0A8L "module-valued Hom-complex cohomology as shifted homotopy Hom"]
noncomputable def homologyHomLinearEquiv (M N : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplex R M N).homology n ≃ₗ[R]
      ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (N⟦n⟧)) where
  toAddEquiv := homologyHomAddEquiv R M N n
  map_smul' := sorry

/-- The canonical linear equivalence factors through the comparison with Mathlib Hom-complex
homology. -/
@[simp]
theorem homologyHomLinearEquiv_apply (M N : CochainComplex C ℤ) (n : ℤ)
    (x : (moduleComplex R M N).homology n) :
    homologyHomLinearEquiv R M N n x =
      CochainComplex.HomComplex.homologyHomAddEquiv M N n
        (homologyAddEquiv R M N n x) := sorry

/-- The homology comparison is natural in both variables of the enriched Hom complex. -/
@[stacks 0A8L "naturality of the module-valued Hom-complex cohomology comparison"]
theorem homologyAddEquiv_naturality
    {M₁ M₂ N₁ N₂ : CochainComplex C ℤ} (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂)
    (n : ℤ) (x : (moduleComplex R M₁ N₁).homology n) :
    homologyAddEquiv R M₂ N₂ n
        (HomologicalComplex.homologyMap (map R f g) n x) =
      HomologicalComplex.homologyMap
        (homComplexPrecomp f ≫ homComplexPostcomp g) n
        (homologyAddEquiv R M₁ N₁ n x) := sorry

/-- The shifted-Hom equivalence is contravariantly natural in the source complex. -/
@[stacks 0A8L "source naturality of enriched Hom-complex cohomology"]
theorem homologyHomLinearEquiv_naturality_source
    {M₁ M₂ N : CochainComplex C ℤ} (f : M₂ ⟶ M₁) (n : ℤ)
    (x : (moduleComplex R M₁ N).homology n) :
    homologyHomLinearEquiv R M₂ N n
        (HomologicalComplex.homologyMap (map R f (𝟙 N)) n x) =
      (HomotopyCategory.quotient C (up ℤ)).map f ≫
        homologyHomLinearEquiv R M₁ N n x := sorry

/-- The shifted-Hom equivalence is covariantly natural in the target complex. -/
@[stacks 0A8L "target naturality of enriched Hom-complex cohomology"]
theorem homologyHomLinearEquiv_naturality_target
    {M N₁ N₂ : CochainComplex C ℤ} (g : N₁ ⟶ N₂) (n : ℤ)
    (x : (moduleComplex R M N₁).homology n) :
    homologyHomLinearEquiv R M N₂ n
        (HomologicalComplex.homologyMap (map R (𝟙 M) g) n x) =
      homologyHomLinearEquiv R M N₁ n x ≫
        (HomotopyCategory.quotient C (up ℤ)).map (g⟦n⟧') := sorry

/-- The shifted-Hom equivalence intertwines the full two-variable Hom-complex map with
precomposition and shifted postcomposition. -/
theorem homologyHomLinearEquiv_naturality
    {M₁ M₂ N₁ N₂ : CochainComplex C ℤ} (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂)
    (n : ℤ) (x : (moduleComplex R M₁ N₁).homology n) :
    homologyHomLinearEquiv R M₂ N₂ n
        (HomologicalComplex.homologyMap (map R f g) n x) =
      (HomotopyCategory.quotient C (up ℤ)).map f ≫
        homologyHomLinearEquiv R M₁ N₁ n x ≫
          (HomotopyCategory.quotient C (up ℤ)).map (g⟦n⟧') := sorry

namespace HomologyHom

/-- Degree-`n` cohomology of the module-valued Hom complex as a bifunctor. -/
@[stacks 0A8L "module-valued Hom-complex cohomology bifunctor"]
noncomputable def bifunctor (n : ℤ) :
    (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤ ModuleCat.{v} R :=
  CochainComplex.HomComplex.bifunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (up ℤ) n

/-- The cohomology bifunctor evaluates to the expected enriched Hom-complex cohomology. -/
@[simp]
theorem bifunctor_obj (n : ℤ)
    (X : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ) :
    (bifunctor R n).obj X = (moduleComplex R X.1.unop X.2).homology n := sorry

/-- The cohomology bifunctor acts by the map on homology induced by the two-variable
Hom-complex map. -/
@[simp]
theorem bifunctor_map (n : ℤ)
    {X Y : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ} (f : X ⟶ Y) :
    (bifunctor R n).map f =
      HomologicalComplex.homologyMap
        (CochainComplex.HomComplex.map R f.1.unop f.2) n := sorry

/-- The quotient functor's shift comparison identifies morphisms into the quotient of a shifted
complex with shifted morphisms between the quotient objects, additively. -/
@[stacks 0A8L "additive quotient-shift comparison"]
noncomputable def quotientShiftAddEquiv
    (M N : CochainComplex C ℤ) (n : ℤ) :
    ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (N⟦n⟧)) ≃+
      ShiftedHom ((HomotopyCategory.quotient C (up ℤ)).obj M)
        ((HomotopyCategory.quotient C (up ℤ)).obj N) n :=
  Iso.homCongrAddEquiv (Iso.refl _)
    (((HomotopyCategory.quotient C (up ℤ)).commShiftIso n).app N)

/-- The additive quotient-shift comparison sends a morphism by postcomposition with the forward
shift comparison. -/
@[simp]
theorem quotientShiftAddEquiv_apply (M N : CochainComplex C ℤ) (n : ℤ)
    (f : (HomotopyCategory.quotient C (up ℤ)).obj M ⟶
      (HomotopyCategory.quotient C (up ℤ)).obj (N⟦n⟧)) :
    quotientShiftAddEquiv M N n f =
      f ≫ ((HomotopyCategory.quotient C (up ℤ)).commShiftIso n).hom.app N := sorry

/-- The quotient functor's shift comparison as the canonical linear congruence on Hom modules. -/
@[stacks 0A8L "linear quotient-shift comparison"]
noncomputable def quotientShiftLinearEquiv
    (M N : CochainComplex C ℤ) (n : ℤ) :
    ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (N⟦n⟧)) ≃ₗ[R]
      ShiftedHom ((HomotopyCategory.quotient C (up ℤ)).obj M)
        ((HomotopyCategory.quotient C (up ℤ)).obj N) n :=
  CategoryTheory.Linear.homCongr R (Iso.refl _)
    (((HomotopyCategory.quotient C (up ℤ)).commShiftIso n).app N)

/-- The linear quotient-shift comparison has the same forward map as its additive form. -/
@[simp]
theorem quotientShiftLinearEquiv_apply (M N : CochainComplex C ℤ) (n : ℤ)
    (f : (HomotopyCategory.quotient C (up ℤ)).obj M ⟶
      (HomotopyCategory.quotient C (up ℤ)).obj (N⟦n⟧)) :
    quotientShiftLinearEquiv R M N n f = quotientShiftAddEquiv M N n f := sorry

/-- The inverse linear quotient-shift comparison postcomposes with the inverse shift
comparison. -/
@[simp]
theorem quotientShiftLinearEquiv_symm_apply (M N : CochainComplex C ℤ) (n : ℤ)
    (f : ShiftedHom ((HomotopyCategory.quotient C (up ℤ)).obj M)
      ((HomotopyCategory.quotient C (up ℤ)).obj N) n) :
    (quotientShiftLinearEquiv R M N n).symm f =
      f ≫ ((HomotopyCategory.quotient C (up ℤ)).commShiftIso n).inv.app N := sorry

/-- Shifted morphisms between the homotopy images of two strict complexes, as a bifunctor. -/
@[stacks 0A8L "shifted homotopy Hom bifunctor on strict complexes"]
noncomputable def shiftedBifunctor (n : ℤ) :
    (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤ ModuleCat.{v} R :=
  ((HomotopyCategory.quotient C (up ℤ)).op.prod
      (HomotopyCategory.quotient C (up ℤ))) ⋙
    Functor.uncurry.obj
      (ShiftedHom.linearCoyoneda R (HomotopyCategory C (up ℤ)) n)

/-- The shifted-Hom bifunctor evaluates to the expected shifted morphism module. -/
@[simp]
theorem shiftedBifunctor_obj (n : ℤ)
    (X : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ) :
    (shiftedBifunctor R n).obj X =
      ModuleCat.of R
        (ShiftedHom ((HomotopyCategory.quotient C (up ℤ)).obj X.1.unop)
          ((HomotopyCategory.quotient C (up ℤ)).obj X.2) n) := sorry

/-- The objectwise linear representation of enriched Hom-complex cohomology by shifted
homotopy morphisms. -/
@[stacks 0A8L "enriched Hom-cohomology linear representation"]
noncomputable def linearEquiv (M N : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplex R M N).homology n ≃ₗ[R]
      ShiftedHom ((HomotopyCategory.quotient C (up ℤ)).obj M)
        ((HomotopyCategory.quotient C (up ℤ)).obj N) n :=
  (homologyHomLinearEquiv R M N n).trans
    (quotientShiftLinearEquiv R M N n)

/-- The enriched Hom-cohomology representation first uses the unshifted Hom comparison and then
the quotient functor's shift comparison. -/
@[simp]
theorem linearEquiv_apply (M N : CochainComplex C ℤ) (n : ℤ)
    (x : (moduleComplex R M N).homology n) :
    linearEquiv R M N n x =
      quotientShiftLinearEquiv R M N n (homologyHomLinearEquiv R M N n x) := sorry

/-- The objectwise Hom-cohomology equivalences commute with the full two-variable functorial
action. -/
theorem naturality (n : ℤ)
    {X Y : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ} (f : X ⟶ Y) :
    (bifunctor R n).map f ≫
        (linearEquiv R Y.1.unop Y.2 n).toModuleIso.hom =
      (linearEquiv R X.1.unop X.2 n).toModuleIso.hom ≫
        (shiftedBifunctor R n).map f := sorry

/-- Module-valued Hom-complex cohomology is naturally isomorphic, in both variables, to
shifted morphisms in the homotopy category. -/
@[stacks 0A8L "natural enriched Hom-cohomology representation"]
noncomputable def iso (n : ℤ) :
    bifunctor (C := C) R n ≅ shiftedBifunctor (C := C) R n :=
  NatIso.ofComponents
    (fun (X : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ) ↦
      (linearEquiv R X.1.unop X.2 n).toModuleIso)
    (fun {_ _} f ↦ naturality R n f)

/-- The natural Hom-cohomology comparison has the canonical linear equivalence as each
component. -/
@[simp]
theorem iso_app (n : ℤ)
    (X : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ) :
    (iso (C := C) R n).app X =
      (linearEquiv R X.1.unop X.2 n).toModuleIso := sorry

end HomologyHom

end CochainComplex.HomComplex.Module
