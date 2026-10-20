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
    s.basis U i = (s.s i).val U := sorry

end GeneratingSections

end SheafOfModules
