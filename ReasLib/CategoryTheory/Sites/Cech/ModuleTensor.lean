/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Bifunctor.Total
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorProduct
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Tensor comparisons for module-valued total Cech complexes

This leaf specializes the heterogeneous total Cech comparison to the genuine tensor product of
modules.  The module carrier universe is independent of the cover-index universe: the latter is
used only for the Cech products, while the former is the carrier of `ModuleCat`.  Thus the
construction applies to `ModuleCat.{uM} ℤ` without requiring a monoidal unit in that category;
the required product-size instance `[HasProducts.{w} (ModuleCat.{uM} R)]` remains explicit at the
boundary because it is a genuine size condition, not a proof-local choice.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uR w uM v u

namespace CategoryTheory.Cech.ModuleTensor

variable {R : Type uR} [CommRing R]
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {ι : Type w}
variable (U : ι → C)
variable (F G : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ)
variable [HasProducts.{w} (ModuleCat.{uM} R)]

/-- The pointwise tensor total of two complexes of module-valued presheaves. -/
@[stacks 07MB "pointwise tensor total of module presheaf complexes"]
abbrev coefficientTensor : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ :=
  HomologicalComplex.mapBifunctor F G
    (ModuleCat.TensorProduct.Presheaf.functor (R := R)) (ComplexShape.up ℤ)

/-- The total Cech functor on module-valued presheaf complexes. -/
@[stacks 07MB "module-valued total Cech functor"]
abbrev cechTotalFunctor :
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ ⥤
      CochainComplex (ModuleCat.{uM} R) ℤ :=
  Cech.Total.totalCechFunctor (A := ModuleCat.{uM} R) U

/-- The total Cech complex of one module-valued presheaf complex. -/
@[stacks 07MB "module-valued total Cech complex"]
abbrev cechTotal (H : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ) :
    CochainComplex (ModuleCat.{uM} R) ℤ :=
  (cechTotalFunctor U).obj H

/-- The tensor total of two module-valued total Cech complexes. -/
@[stacks 07MB "source of the module-valued total Cech tensor comparison"]
abbrev source : CochainComplex (ModuleCat.{uM} R) ℤ :=
  Bifunctor.Total.source (ModuleCat.TensorProduct.functor.{uR, uM, uM} R) U F G

/-- The total Cech complex of the pointwise tensor total of two module-valued complexes. -/
@[stacks 07MB "target of the module-valued total Cech tensor comparison"]
abbrev target : CochainComplex (ModuleCat.{uM} R) ℤ :=
  Bifunctor.Total.target (ModuleCat.TensorProduct.functor.{uR, uM, uM} R) U F G

/-- The canonical comparison from the tensor total of two module-valued Cech totals to the Cech
total of their pointwise tensor total.  For `R := ℤ`, this is the comparison of 20.25.3.2 (07MB). -/
@[stacks 07MB "module-valued total Cech tensor comparison"]
noncomputable abbrev comparison : source U F G ⟶ target U F G :=
  Bifunctor.Total.comparison (ModuleCat.TensorProduct.functor.{uR, uM, uM} R) U F G

/-- The module-valued total Čech comparison is natural in both coefficient complexes. -/
@[reassoc, stacks 07MB "naturality of the module-valued Cech tensor comparison"]
theorem comparison_naturality
    {F' G' : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ} (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap
        ((cechTotalFunctor U).map f) ((cechTotalFunctor U).map g)
        (ModuleCat.TensorProduct.functor.{uR, uM, uM} R) (ComplexShape.up ℤ) ≫
      comparison U F' G' =
    comparison U F G ≫
      (cechTotalFunctor U).map
        (HomologicalComplex.mapBifunctorMap f g
          (ModuleCat.TensorProduct.Presheaf.functor (R := R)) (ComplexShape.up ℤ)) := sorry

/- The degree component is kept at this specialization boundary so module-valued consumers do not
reopen the heterogeneous coefficient bifunctor just to access the canonical four-degree map. -/
/-- The degree-`n` component of the module-valued total Čech tensor comparison. -/
@[simp, stacks 07MB "degree component of the module-valued Cech tensor comparison"]
theorem comparison_f (n : ℤ) :
    (comparison U F G).f n =
      Bifunctor.Total.componentMap (ModuleCat.TensorProduct.functor.{uR, uM, uM} R)
        U F G n (fun _ _ h ↦
          Bifunctor.Total.component
            (ModuleCat.TensorProduct.functor.{uR, uM, uM} R) U F G n h) := sorry

/-- Compose the canonical Cech tensor comparison with a pairing of coefficient complexes. -/
@[stacks 07MB "Cech tensor comparison followed by a coefficient pairing"]
noncomputable abbrev pairing
    {H : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ}
    (γ : coefficientTensor F G ⟶ H) :
    source U F G ⟶ cechTotal U H :=
  comparison U F G ≫
    (cechTotalFunctor U).map γ

/-- The degree-`n` component after composing the comparison with a coefficient pairing. -/
@[simp, stacks 07MB "degree component after a module-valued Cech pairing"]
theorem pairing_f
    {H : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{uM} R) ℤ}
    (γ : coefficientTensor F G ⟶ H) (n : ℤ) :
    (pairing U F G γ).f n =
      (comparison U F G).f n ≫ ((cechTotalFunctor U).map γ).f n := sorry

end CategoryTheory.Cech.ModuleTensor

end
