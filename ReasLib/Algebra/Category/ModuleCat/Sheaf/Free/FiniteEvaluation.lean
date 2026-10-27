/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Evaluation of finite free module sheaves

A finite free sheaf evaluates to the corresponding finite function module. An isomorphic
finite generating family therefore gives an actual basis of the module of sections on each
object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Evaluation of a finite free module sheaf is the finite function module over the
coefficient ring on the chosen object. -/
def freeEvaluationIso (I : Type w) [Finite I] (U : Cᵒᵖ) :
    (evaluation R U).obj (free I) ≅ ModuleCat.of (R.obj.obj U) (I → R.obj.obj U) := by
  letI : HasFiniteBiproducts (SheafOfModules.{w} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact (evaluation R U).mapIso (biproductIso (fun _ : I ↦ unit R)).symm ≪≫
    PreservesProduct.iso (evaluation R U) (fun _ : I ↦ unit R) ≪≫
    ModuleCat.piIsoPi (fun _ : I ↦ (evaluation R U).obj (unit R))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation identifies the tautological free sections with the coordinate vectors. -/
theorem freeEvaluationIso_freeSection (I : Type w) [Finite I] (U : Cᵒᵖ) (i : I) :
    (freeEvaluationIso R I U).hom ((freeSection (R := R) i).val U) =
      Pi.basisFun (R.obj.obj U) I i := by
  classical
  letI : HasFiniteBiproducts (SheafOfModules.{w} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have h (j : I) :
      ιFree (R := R) i ≫ (biproductIso (fun _ : I ↦ unit R)).inv ≫
          Pi.π (fun _ : I ↦ unit R) j =
        if h : i = j then eqToHom (congrArg (fun _ : I ↦ unit R) h) else 0 := by
    change Sigma.ι (fun _ : I ↦ unit R) i ≫
        (biproduct.isoCoproduct (fun _ : I ↦ unit R)).inv ≫
        (biproduct.isoProduct (fun _ : I ↦ unit R)).hom ≫
        Pi.π (fun _ : I ↦ unit R) j = _
    rw [biproduct.isoCoproduct_inv, biproduct.isoProduct_hom,
      ← Category.assoc, ← Category.assoc, Sigma.ι_desc, Category.assoc, Pi.lift_π,
      biproduct.ι_π]
  have hc (j : I) :
      (evaluation R U).map (ιFree (R := R) i) ≫ (freeEvaluationIso R I U).hom ≫
          ModuleCat.ofHom (LinearMap.proj j) =
        (evaluation R U).map
          (if h : i = j then eqToHom (congrArg (fun _ : I ↦ unit R) h) else 0) := by
    simp only [freeEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      PreservesProduct.iso_hom, piComparison_comp_π]
    simpa only [Functor.map_comp, Category.assoc] using congrArg ((evaluation R U).map) (h j)
  ext j
  have hj := congrArg (fun f ↦ f (1 : R.obj.obj U)) (hc j)
  by_cases hij : i = j
  · subst j
    convert hj using 1 <;>
      simp [freeSection, freeHomEquiv, Pi.basisFun_apply, evaluation] <;> rfl
  · convert hj using 1 <;>
      simp [freeSection, freeHomEquiv, Pi.basisFun_apply, evaluation,
        hij, Ne.symm hij] <;> rfl

namespace GeneratingSections

variable {R} {M : SheafOfModules.{w} R} (s : M.GeneratingSections)
    [s.IsFiniteType] [IsIso s.π]

/-- A finite generating family whose presentation is an isomorphism supplies a basis
of the module of sections on each object. -/
def basis (U : Cᵒᵖ) : Module.Basis s.I (R.obj.obj U) (M.val.obj U) := by
  letI := Fintype.ofFinite s.I
  exact (Pi.basisFun (R.obj.obj U) s.I).map
    ((freeEvaluationIso R s.I U).symm ≪≫ (evaluation R U).mapIso (asIso s.π)).toLinearEquiv

/-- The basis vectors are the evaluations of the specified generating sections. -/
theorem basis_apply (U : Cᵒᵖ) (i : s.I) :
    s.basis U i = (s.s i).val U := by
  classical
  rw [basis, Module.Basis.map_apply,
    ← freeEvaluationIso_freeSection R s.I U i]
  change s.π.val.app U
      ((freeEvaluationIso R s.I U).inv
        ((freeEvaluationIso R s.I U).hom ((freeSection (R := R) i).val U))) = _
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id]
  exact congrArg (fun t ↦ t.val U)
    (sectionsMap_freeHomEquiv_symm_freeSection s.s i)

/-- The evaluated bases commute with restriction, with the coefficient map supplied by
the sheaf of rings. -/
theorem map_basis {U V : Cᵒᵖ} (f : U ⟶ V) (i : s.I) :
    M.val.map f (s.basis U i) = s.basis V i := by
  rw [basis_apply, basis_apply]
  exact PresheafOfModules.sections_property (s.s i) f

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates in an evaluated finite basis restrict coefficient by coefficient. -/
theorem repr_map {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (i : s.I) :
    (s.basis V).repr (M.val.map f x) i =
      R.obj.map f ((s.basis U).repr x i) := by
  classical
  letI := Fintype.ofFinite s.I
  conv_lhs => rw [← (s.basis U).sum_repr x]
  simp only [map_sum, PresheafOfModules.map_smul, map_basis]
  simpa only [map_sum] using congrFun ((s.basis V).repr_sum_self
    (fun j ↦ R.obj.map f ((s.basis U).repr x j))) i

end GeneratingSections

end SheafOfModules
