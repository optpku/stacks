/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts of module presheaves

Coproducts of dependent module presheaves are computed objectwise. This file packages the
evaluation isomorphism and the formulas needed to compare it with coproduct inclusions, maps,
and restriction morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe t u v w

namespace PresheafOfModules.Coproduct

variable {C : Type u} [Category.{v} C]
variable {R : Cᵒᵖ ⥤ RingCat.{w}}
variable {ι : Type t}
variable [Small.{w} ι]

/-- Evaluation of a coproduct of module presheaves is the coproduct of their evaluations. -/
@[stacks 01CF "objectwise coproduct of module presheaves"]
noncomputable def evaluationIso
    (F : ι → PresheafOfModules.{w} R) (U : Cᵒᵖ) :
    (∐ F).obj U ≅ ∐ fun i : ι ↦ (F i).obj U :=
  PreservesCoproduct.iso (PresheafOfModules.evaluation R U) F

/-- A presheaf coproduct inclusion evaluates to the corresponding module coproduct
inclusion. -/
@[reassoc (attr := simp)]
theorem ι_evaluationIso_hom
    (F : ι → PresheafOfModules.{w} R) (i : ι) (U : Cᵒᵖ) :
    (Limits.Sigma.ι F i).app U ≫ (evaluationIso F U).hom =
      Limits.Sigma.ι (fun i : ι ↦ (F i).obj U) i := sorry

/-- Evaluation carries a coproduct map to the coproduct of the evaluated component maps. -/
theorem map_evaluationIso_hom
    {F G : ι → PresheafOfModules.{w} R}
    (f : ∀ i : ι, F i ⟶ G i) (U : Cᵒᵖ) :
    (Limits.Sigma.map f).app U ≫ (evaluationIso G U).hom =
      (evaluationIso F U).hom ≫
        Limits.Sigma.map (fun i : ι ↦ (f i).app U) := sorry

/-- The inverse evaluation comparison intertwines a coproduct map with the coproduct of the
evaluated component maps. -/
theorem evaluationIso_inv_map
    {F G : ι → PresheafOfModules.{w} R}
    (f : ∀ i : ι, F i ⟶ G i) (U : Cᵒᵖ) :
    (evaluationIso F U).inv ≫ (Limits.Sigma.map f).app U =
      Limits.Sigma.map (fun i : ι ↦ (f i).app U) ≫
        (evaluationIso G U).inv := sorry

/-- The objectwise coproduct comparison intertwines the restriction morphism of a coproduct
presheaf with the coproduct of the component restrictions. -/
theorem restriction_evaluationIso_hom
    (F : ι → PresheafOfModules.{w} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (∐ F).map f ≫
        (ModuleCat.restrictScalars (R.map f).hom).map
          (evaluationIso F V).hom =
      (evaluationIso F U).hom ≫
        Limits.Sigma.map (fun i : ι ↦ (F i).map f) ≫
        (PreservesCoproduct.iso (ModuleCat.restrictScalars (R.map f).hom)
          (fun i : ι ↦ (F i).obj V)).inv := sorry

/-- The inverse objectwise comparison writes restriction of a presheaf coproduct as the
coproduct of the component restrictions. -/
theorem evaluationIso_inv_restriction
    (F : ι → PresheafOfModules.{w} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (evaluationIso F U).inv ≫ (∐ F).map f =
      Limits.Sigma.map (fun i : ι ↦ (F i).map f) ≫
        (PreservesCoproduct.iso (ModuleCat.restrictScalars (R.map f).hom)
          (fun i : ι ↦ (F i).obj V)).inv ≫
        (ModuleCat.restrictScalars (R.map f).hom).map
          (evaluationIso F V).inv := sorry

end PresheafOfModules.Coproduct
