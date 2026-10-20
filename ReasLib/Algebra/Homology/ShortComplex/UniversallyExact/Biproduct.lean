/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Biproducts
public import ReasLib.LinearAlgebra.UniversallyInjective.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Biproduct stability of universal exactness

@stack 058N

This leaf owns the reusable binary-biproduct closure statements for short
complexes of modules.  The source-facing examples only need to import this
file; concrete integer and non-flat constructions remain in their chapter.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

local instance hasBinaryBiproductπ₁ (S T : ShortComplex (ModuleCat.{v} R)) :
    HasBinaryBiproduct ((ShortComplex.π₁ : _ ⥤ ModuleCat.{v} R).obj S)
      ((ShortComplex.π₁ : _ ⥤ ModuleCat.{v} R).obj T) := by
  infer_instance

local instance hasBinaryBiproductπ₂ (S T : ShortComplex (ModuleCat.{v} R)) :
    HasBinaryBiproduct ((ShortComplex.π₂ : _ ⥤ ModuleCat.{v} R).obj S)
      ((ShortComplex.π₂ : _ ⥤ ModuleCat.{v} R).obj T) := by
  infer_instance

local instance hasBinaryBiproductπ₃ (S T : ShortComplex (ModuleCat.{v} R)) :
    HasBinaryBiproduct ((ShortComplex.π₃ : _ ⥤ ModuleCat.{v} R).obj S)
      ((ShortComplex.π₃ : _ ⥤ ModuleCat.{v} R).obj T) := by
  infer_instance

noncomputable local instance preservesBinaryBiproductπ₁
    (S T : ShortComplex (ModuleCat.{v} R)) :
    PreservesBinaryBiproduct S T (ShortComplex.π₁ : _ ⥤ ModuleCat.{v} R) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

noncomputable local instance preservesBinaryBiproductπ₂
    (S T : ShortComplex (ModuleCat.{v} R)) :
    PreservesBinaryBiproduct S T (ShortComplex.π₂ : _ ⥤ ModuleCat.{v} R) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

noncomputable local instance preservesBinaryBiproductπ₃
    (S T : ShortComplex (ModuleCat.{v} R)) :
    PreservesBinaryBiproduct S T (ShortComplex.π₃ : _ ⥤ ModuleCat.{v} R) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

set_option backward.defeqAttrib.useBackward true in
noncomputable def biprodX₁Iso (S T : ShortComplex (ModuleCat.{v} R)) :
    (S ⊞ T).X₁ ≅ S.X₁ ⊞ T.X₁ :=
  ShortComplex.π₁.mapBiprod S T

set_option backward.defeqAttrib.useBackward true in
noncomputable def biprodX₂Iso (S T : ShortComplex (ModuleCat.{v} R)) :
    (S ⊞ T).X₂ ≅ S.X₂ ⊞ T.X₂ :=
  ShortComplex.π₂.mapBiprod S T

set_option backward.defeqAttrib.useBackward true in
noncomputable def biprodX₃Iso (S T : ShortComplex (ModuleCat.{v} R)) :
    (S ⊞ T).X₃ ≅ S.X₃ ⊞ T.X₃ :=
  ShortComplex.π₃.mapBiprod S T

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem biprodX₁Iso_hom_fst (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₁Iso S T).hom ≫ biprod.fst = (biprod.fst : S ⊞ T ⟶ S).τ₁ := by
  simp [biprodX₁Iso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem biprodX₁Iso_hom_snd (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₁Iso S T).hom ≫ biprod.snd = (biprod.snd : S ⊞ T ⟶ T).τ₁ := by
  simp [biprodX₁Iso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem biprodX₂Iso_hom_fst (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₂Iso S T).hom ≫ biprod.fst = (biprod.fst : S ⊞ T ⟶ S).τ₂ := by
  simp [biprodX₂Iso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem biprodX₂Iso_hom_snd (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₂Iso S T).hom ≫ biprod.snd = (biprod.snd : S ⊞ T ⟶ T).τ₂ := by
  simp [biprodX₂Iso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem biprodX₃Iso_hom_fst (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₃Iso S T).hom ≫ biprod.fst = (biprod.fst : S ⊞ T ⟶ S).τ₃ := by
  simp [biprodX₃Iso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem biprodX₃Iso_hom_snd (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₃Iso S T).hom ≫ biprod.snd = (biprod.snd : S ⊞ T ⟶ T).τ₃ := by
  simp [biprodX₃Iso]

private theorem biprodProductIso_f (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₁Iso S T ≪≫
        ModuleCat.biprodIsoProd S.X₁ T.X₁).hom ≫
          ModuleCat.ofHom (S.f.hom.prodMap T.f.hom) =
      (S ⊞ T).f ≫ (biprodX₂Iso S T ≪≫
        ModuleCat.biprodIsoProd S.X₂ T.X₂).hom := by
  have hmap : (biprodX₁Iso S T).hom ≫ biprod.map S.f T.f =
      (S ⊞ T).f ≫ (biprodX₂Iso S T).hom := by
    rw [biprod.ext_to_iff]
    constructor
    · simpa [Category.assoc] using (biprod.fst : S ⊞ T ⟶ S).comm₁₂
    · simpa [Category.assoc] using (biprod.snd : S ⊞ T ⟶ T).comm₁₂
  simp only [Iso.trans_hom]
  calc
    _ = (biprodX₁Iso S T).hom ≫ biprod.map S.f T.f ≫
        (ModuleCat.biprodIsoProd S.X₂ T.X₂).hom := by
      rw [Category.assoc, ModuleCat.biprod_map_comp_biprodIsoProd_hom]
    _ = ((biprodX₁Iso S T).hom ≫ biprod.map S.f T.f) ≫
        (ModuleCat.biprodIsoProd S.X₂ T.X₂).hom := by simp
    _ = ((S ⊞ T).f ≫ (biprodX₂Iso S T).hom) ≫
        (ModuleCat.biprodIsoProd S.X₂ T.X₂).hom := by rw [hmap]
    _ = _ := by simp [Category.assoc]

private theorem biprodProductIso_g (S T : ShortComplex (ModuleCat.{v} R)) :
    (biprodX₂Iso S T ≪≫
        ModuleCat.biprodIsoProd S.X₂ T.X₂).hom ≫
          ModuleCat.ofHom (S.g.hom.prodMap T.g.hom) =
      (S ⊞ T).g ≫ (biprodX₃Iso S T ≪≫
        ModuleCat.biprodIsoProd S.X₃ T.X₃).hom := by
  have hmap : (biprodX₂Iso S T).hom ≫ biprod.map S.g T.g =
      (S ⊞ T).g ≫ (biprodX₃Iso S T).hom := by
    rw [biprod.ext_to_iff]
    constructor
    · simpa [Category.assoc] using (biprod.fst : S ⊞ T ⟶ S).comm₂₃
    · simpa [Category.assoc] using (biprod.snd : S ⊞ T ⟶ T).comm₂₃
  simp only [Iso.trans_hom]
  calc
    _ = (biprodX₂Iso S T).hom ≫ biprod.map S.g T.g ≫
        (ModuleCat.biprodIsoProd S.X₃ T.X₃).hom := by
      rw [Category.assoc, ModuleCat.biprod_map_comp_biprodIsoProd_hom]
    _ = ((biprodX₂Iso S T).hom ≫ biprod.map S.g T.g) ≫
        (ModuleCat.biprodIsoProd S.X₃ T.X₃).hom := by simp
    _ = ((S ⊞ T).g ≫ (biprodX₃Iso S T).hom) ≫
        (ModuleCat.biprodIsoProd S.X₃ T.X₃).hom := by rw [hmap]
    _ = _ := by simp [Category.assoc]

private noncomputable def biprodX₁LinearEquiv (S T : ShortComplex (ModuleCat.{v} R)) :
    (S ⊞ T).X₁ ≃ₗ[R] S.X₁ × T.X₁ :=
  (biprodX₁Iso S T ≪≫ ModuleCat.biprodIsoProd S.X₁ T.X₁).toLinearEquiv

private noncomputable def biprodX₂LinearEquiv (S T : ShortComplex (ModuleCat.{v} R)) :
    (S ⊞ T).X₂ ≃ₗ[R] S.X₂ × T.X₂ :=
  (biprodX₂Iso S T ≪≫ ModuleCat.biprodIsoProd S.X₂ T.X₂).toLinearEquiv

private theorem biprodProductLinearEquiv_f (S T : ShortComplex (ModuleCat.{v} R)) :
    (S.f.hom.prodMap T.f.hom).comp (biprodX₁LinearEquiv S T).toLinearMap =
      (biprodX₂LinearEquiv S T).toLinearMap.comp (S ⊞ T).f.hom := by
  exact congrArg ModuleCat.Hom.hom (biprodProductIso_f S T)

namespace ShortExact

/-- Binary biproducts preserve short exactness for short complexes of modules. -/
@[stacks 058N "short exactness is stable under binary biproducts"]
theorem biprod {S T : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (hT : T.ShortExact) :
    (S ⊞ T).ShortExact := by
  have hExactS : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hExactT : Function.Exact T.f.hom T.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact
  have hExactProd : Function.Exact
      (S.f.hom.prodMap T.f.hom) (S.g.hom.prodMap T.g.hom) := by
    rw [LinearMap.exact_iff, LinearMap.ker_prodMap, LinearMap.range_prodMap,
      hExactS.linearMap_ker_eq, hExactT.linearMap_ker_eq]
  let P : ShortComplex (ModuleCat.{v} R) :=
    ModuleCat.shortComplexOfCompEqZero (S.f.hom.prodMap T.f.hom)
      (S.g.hom.prodMap T.g.hom) hExactProd.linearMap_comp_eq_zero
  have hP : P.ShortExact := ModuleCat.shortComplex_shortExact P hExactProd
    (hS.moduleCat_injective_f.prodMap hT.moduleCat_injective_f)
    (hS.moduleCat_surjective_g.prodMap hT.moduleCat_surjective_g)
  let e₁ : (S ⊞ T).X₁ ≅ ModuleCat.of R (S.X₁ × T.X₁) :=
    biprodX₁Iso S T ≪≫ ModuleCat.biprodIsoProd S.X₁ T.X₁
  let e₂ : (S ⊞ T).X₂ ≅ ModuleCat.of R (S.X₂ × T.X₂) :=
    biprodX₂Iso S T ≪≫ ModuleCat.biprodIsoProd S.X₂ T.X₂
  let e₃ : (S ⊞ T).X₃ ≅ ModuleCat.of R (S.X₃ × T.X₃) :=
    biprodX₃Iso S T ≪≫ ModuleCat.biprodIsoProd S.X₃ T.X₃
  let e : (S ⊞ T) ≅ P := ShortComplex.isoMk e₁ e₂ e₃
    (by simpa [P, e₁, e₂] using biprodProductIso_f S T)
    (by simpa [P, e₂, e₃] using biprodProductIso_g S T)
  exact ShortComplex.shortExact_of_iso e.symm hP

end ShortExact

variable {R : Type u} [CommRing R]

private theorem universallyInjective_biprod_product_comp
    {S T : ShortComplex (ModuleCat.{v} R)}
    (hS : LinearMap.UniversallyInjective.{u, v, v, max u v} S.f.hom)
    (hT : LinearMap.UniversallyInjective.{u, v, v, max u v} T.f.hom) :
    LinearMap.UniversallyInjective.{u, v, v, max u v}
      ((S.f.hom.prodMap T.f.hom).comp
        (biprodX₁LinearEquiv S T).toLinearMap) :=
  LinearMap.universallyInjective_comp
    (LinearMap.UniversallyInjective.prodMap hS hT)
    (biprodX₁LinearEquiv S T).universallyInjective

private theorem universallyInjective_biprod_conjugate
    {S T : ShortComplex (ModuleCat.{v} R)}
    (hS : LinearMap.UniversallyInjective.{u, v, v, max u v} S.f.hom)
    (hT : LinearMap.UniversallyInjective.{u, v, v, max u v} T.f.hom) :
    LinearMap.UniversallyInjective.{u, v, v, max u v}
      ((biprodX₂LinearEquiv S T).toLinearMap.comp (S ⊞ T).f.hom) :=
  (universallyInjective_biprod_product_comp hS hT).congr
    (biprodProductLinearEquiv_f S T)

private theorem universallyInjective_biprod_f
    {S T : ShortComplex (ModuleCat.{v} R)}
    (hS : LinearMap.UniversallyInjective.{u, v, v, max u v} S.f.hom)
    (hT : LinearMap.UniversallyInjective.{u, v, v, max u v} T.f.hom) :
    LinearMap.UniversallyInjective.{u, v, v, max u v} (S ⊞ T).f.hom :=
  LinearMap.universallyInjective_of_comp
    (universallyInjective_biprod_conjugate hS hT)

namespace UniversallyExact

/-- Universal exactness is stable under binary biproducts of module short complexes. -/
@[stacks 058N "universal exactness is stable under binary biproducts"]
theorem biprod {S T : ShortComplex (ModuleCat.{v} R)}
    (hS : S.UniversallyExact) (hT : T.UniversallyExact) :
    (S ⊞ T).UniversallyExact :=
  ⟨hS.shortExact.biprod hT.shortExact,
    universallyInjective_biprod_f hS.universallyInjective_f hT.universallyInjective_f⟩

end UniversallyExact

section Checks

end Checks

end CategoryTheory.ShortComplex
