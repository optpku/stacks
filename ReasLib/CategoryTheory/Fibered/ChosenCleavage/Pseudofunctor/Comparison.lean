/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Comparison

/-!
# Comparing explicit and selected fiber pseudofunctors

This file is the application boundary between an arbitrary explicit cleavage and the cleavage
selected from a fibred projection. The comparison data remains owned by the neutral
change-of-cleavage API.
-/

@[expose] public section

universe vC vS uC uS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.Cleavage

variable {p : S ⥤ C}

private theorem comparison_inverse_naturality
    (chi₁ chi₂ : p.Cleavage) {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) :
    (toPseudofunctor.uniqueEquivalence chi₁ chi₂).inv.naturality f =
      (toPseudofunctor.uniqueStrongTrans chi₂ chi₁).naturality f := by
  apply Iso.ext
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  -- The mate along identity component equivalences inserts only identity maps.
  change (𝟙 _ ≫
    (𝟙 _ ≫ (chi₂.reindex f.as.unop).map (𝟙 _ ≫ 𝟙 _) ≫
      𝟙 _ ≫ (Reindex.uniqueIsoApp chi₁ chi₂ f.as.unop x).inv) ≫
    𝟙 _) ≫ 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The fiber pseudofunctor for an explicit cleavage is canonically equivalent to the one
obtained from the selected cleavage of a fibred projection. -/
@[stacks 02XO "independence of the selected cleavage"]
noncomputable def toPseudofunctor.selectedEquivalence
    (chi : p.Cleavage) [p.IsFibered] :
    chi.toPseudofunctor ≌ fiberPseudofunctor p :=
  toPseudofunctor.uniqueEquivalence chi (Cleavage.ofIsFibered p)

/-- The forward transformation of the explicit-to-selected equivalence is the canonical
change-of-cleavage transformation. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.hom
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).hom =
      toPseudofunctor.uniqueStrongTrans chi (Cleavage.ofIsFibered p) := by
  rfl

/-- The inverse transformation of the explicit-to-selected equivalence is the canonical
comparison back to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inv
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).inv =
      toPseudofunctor.uniqueStrongTrans (Cleavage.ofIsFibered p) chi := by
  change Pseudofunctor.StrongTrans.mk _ _ _ _ _ =
    Pseudofunctor.StrongTrans.mk _ _ _ _ _
  congr 1
  funext a b f
  exact comparison_inverse_naturality chi (Cleavage.ofIsFibered p) f

/-- The indexed presentation of the forward explicit-to-selected comparison is the canonical
change from the explicit cleavage to the selected cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.hom.toIndexedFunctor
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).hom.toIndexedFunctor =
      Indexed.comparison chi (Cleavage.ofIsFibered p) := by
  rfl

/-- The indexed presentation of the inverse selected-to-explicit comparison is the canonical
change from the selected cleavage to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inv.toIndexedFunctor
    (chi : p.Cleavage) [p.IsFibered] :
    (toPseudofunctor.selectedEquivalence chi).inv.toIndexedFunctor =
      Indexed.comparison (Cleavage.ofIsFibered p) chi := by
  rw [toPseudofunctor.selectedEquivalence.inv]
  rfl

/-- Components of the forward explicit-to-selected comparison are identity functors on the
standard fibers. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.hom.app
    (chi : p.Cleavage) [p.IsFibered] (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.selectedEquivalence chi).hom.app a =
      𝟙 (chi.toPseudofunctor.obj a) := by
  rfl

/-- Components of the inverse selected-to-explicit comparison are identity functors on the
standard fibers. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inv.app
    (chi : p.Cleavage) [p.IsFibered] (a : LocallyDiscrete Cᵒᵖ) :
    (toPseudofunctor.selectedEquivalence chi).inv.app a =
      𝟙 ((fiberPseudofunctor p).obj a) := by
  rfl

/-- Objectwise forward naturality of the explicit-to-selected comparison is the canonical
comparison between the corresponding reindexing functors. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.forward.naturality.hom.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).hom.naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi (Cleavage.ofIsFibered p) f.as.unop x).hom := by
  rfl

/-- Objectwise inverse naturality of the explicit-to-selected comparison is the inverse
canonical comparison between the corresponding reindexing functors. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.forward.naturality.inv.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).hom.naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp chi (Cleavage.ofIsFibered p) f.as.unop x).inv := by
  rfl

/-- Objectwise forward naturality of the selected-to-explicit inverse comparison is the
canonical comparison back to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inverse.naturality.hom.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).inv.naturality f).hom.toNatTrans.app x =
      (Reindex.uniqueIsoApp (Cleavage.ofIsFibered p) chi f.as.unop x).hom := by
  change ((toPseudofunctor.uniqueEquivalence chi
    (Cleavage.ofIsFibered p)).inv.naturality f).hom.toNatTrans.app x = _
  rw [comparison_inverse_naturality]
  rfl

/-- Objectwise inverse naturality of the selected-to-explicit inverse comparison is the
inverse canonical comparison back to the explicit cleavage. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.inverse.naturality.inv.app
    (chi : p.Cleavage) [p.IsFibered]
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (x : Fiber p (unop a.as)) :
    ((toPseudofunctor.selectedEquivalence chi).inv.naturality f).inv.toNatTrans.app x =
      (Reindex.uniqueIsoApp (Cleavage.ofIsFibered p) chi f.as.unop x).inv := by
  change ((toPseudofunctor.uniqueEquivalence chi
    (Cleavage.ofIsFibered p)).inv.naturality f).inv.toNatTrans.app x = _
  rw [comparison_inverse_naturality]
  rfl

/-- Selecting the already selected cleavage gives the identity pseudofunctor equivalence. -/
@[simp]
theorem toPseudofunctor.selectedEquivalence.self [p.IsFibered] :
    toPseudofunctor.selectedEquivalence (Cleavage.ofIsFibered p) =
      Bicategory.Equivalence.id (fiberPseudofunctor p) := by
  have hh : toPseudofunctor.uniqueStrongTrans (Cleavage.ofIsFibered p)
      (Cleavage.ofIsFibered p) = Pseudofunctor.StrongTrans.id (fiberPseudofunctor p) := by
    let chi := Cleavage.ofIsFibered p
    change Pseudofunctor.StrongTrans.mk _ _ _ _ _ = Pseudofunctor.StrongTrans.mk _ _ _ _ _
    congr 1
    funext a b f
    apply Iso.ext
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    apply Subtype.ext
    letI : p.IsStronglyCartesian f.as.unop (chi.cartesianHom f.as.unop x) :=
      (chi.reindexLift f.as.unop x).isStronglyCartesian
    change IsStronglyCartesian.map p f.as.unop (chi.cartesianHom f.as.unop x)
      (Category.id_comp f.as.unop).symm (chi.cartesianHom f.as.unop x) = 𝟙 _ ≫ 𝟙 _
    simp only [IsStronglyCartesian.map_self, Category.id_comp]
  have hi : (toPseudofunctor.selectedEquivalence (Cleavage.ofIsFibered p)).inv =
      Pseudofunctor.StrongTrans.id (fiberPseudofunctor p) :=
    (toPseudofunctor.selectedEquivalence.inv (Cleavage.ofIsFibered p)).trans hh
  have hIso {η θ η' θ' : (fiberPseudofunctor p) ⟶ fiberPseudofunctor p}
      (hη : η = η') (hθ : θ = θ') (e : η ≅ θ) (e' : η' ≅ θ')
      (h : HEq (fun a ↦ e.hom.as.app a) (fun a ↦ e'.hom.as.app a)) : HEq e e' := by
    cases hη
    cases hθ
    apply heq_of_eq
    apply Iso.ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    exact congrFun (eq_of_heq h) a
  change Bicategory.Equivalence.mk _ _ _ _ _ = Bicategory.Equivalence.mk _ _ _ _ _
  congr 1
  · apply hIso rfl (congrArg₂ Pseudofunctor.StrongTrans.vcomp hh hi)
    apply heq_of_eq
    funext a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  · apply hIso (congrArg₂ Pseudofunctor.StrongTrans.vcomp hi hh) rfl
    apply heq_of_eq
    funext a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  · apply proof_irrel_heq

end Functor.Cleavage

end CategoryTheory
