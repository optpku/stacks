/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

/-!
# Naturality of cartesian-functor reindexing comparisons

This module gives fiber, total-category, pseudofunctor-map, and conjugation forms of the
objectwise reindexing comparison.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

universe uS₁ vS₁ uS₂ vS₂

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise reindexing comparison is natural in the source fiber object. -/
theorem Reindex.mapIso.hom.naturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (f⁎[χ₂]).map ((F.fiberFunctor U).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom =
      (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (F.fiberFunctor V).map ((f⁎[χ₁]).map α) := by
  letI : p₂.IsStronglyCartesian f (F.toFunctor.map (χ₁.cartesianHom f y)) :=
    Map.stronglyCartesianOfLift F f (χ₁.cartesianHom f y)
      (Functor.Cleavage.cartesianHom.isStronglyCartesian χ₁ f y)
  letI := (((f⁎[χ₂]).map ((F.fiberFunctor U).map α)) ≫
    (Reindex.mapIso F χ₁ χ₂ f y).hom).2
  letI := ((Reindex.mapIso F χ₁ χ₂ f x).hom ≫
    (F.fiberFunctor V).map ((f⁎[χ₁]).map α)).2
  apply Functor.Fiber.hom_ext
  apply Functor.IsStronglyCartesian.ext p₂ f
    (F.toFunctor.map (χ₁.cartesianHom f y)) (𝟙 V)
  change
    (((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom.1) ≫
          F.toFunctor.map (χ₁.cartesianHom f y) =
      ((Reindex.mapIso F χ₁ χ₂ f x).hom.1 ≫
        F.toFunctor.map ((f⁎[χ₁]).map α).1) ≫
          F.toFunctor.map (χ₁.cartesianHom f y)
  have hmap := congrArg F.toFunctor.map (Functor.Cleavage.reindex.map_fac χ₁ f α)
  simp only [Functor.map_comp] at hmap
  simp only [Category.assoc, Reindex.mapIso.hom.fac]
  rw [hmap, ← Category.assoc, Reindex.mapIso.hom.fac]
  exact Functor.Cleavage.reindex.map_fac χ₂ f ((F.fiberFunctor U).map α)
/- Proof strategy: forget to the total category and postcompose with the target cartesian arrow;
use the two factorization identities and functoriality to reduce both sides to the same map. -/

/-- Naturality of the forward comparison after forgetting fiber morphisms to the target total
category. -/
@[reassoc]
theorem Reindex.mapIso.hom.naturalityTotal
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom.1 =
      (Reindex.mapIso F χ₁ χ₂ f x).hom.1 ≫
        ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 := by
  exact congrArg (fun k ↦ k.1) (Reindex.mapIso.hom.naturality F χ₁ χ₂ f α)
/- Proof strategy: apply `congrArg (fun k ↦ k.1)` to
`Reindex.mapIso.hom.naturality F χ₁ χ₂ f α`. -/

/-- Naturality of the forward reindexing comparison in the map presentation of the canonical
fiber pseudofunctors.

This is the source-facing form for descent and `pullHom` calculations associated with the two
displayed cleavages. -/
theorem Reindex.mapIso.hom.mapNaturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (χ₂.toPseudofunctor.map f.op.toLoc).toFunctor.map
          ((F.fiberFunctor U).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom =
      (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (F.fiberFunctor V).map
          ((χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.map α) := by
  exact Reindex.mapIso.hom.naturality F χ₁ χ₂ f α
/- Proof strategy: transport `Reindex.mapIso.hom.naturality F χ₁ χ₂ f α` across
`toPseudofunctor.mapIso χ₁` and `toPseudofunctor.mapIso χ₂`; both bridges are `eqToIso`, so
equality elimination reduces the statement to the cleavage presentation. -/

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inverse reindexing comparison. -/
theorem Reindex.mapIso.inv.naturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (F.fiberFunctor V).map ((f⁎[χ₁]).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv =
      (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (f⁎[χ₂]).map ((F.fiberFunctor U).map α) := by
  apply (cancel_mono (Reindex.mapIso F χ₁ χ₂ f y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Reindex.mapIso.hom.naturality F χ₁ χ₂ f α, Iso.inv_hom_id_assoc]
/- Proof strategy: conjugate `Reindex.mapIso.hom.naturality F χ₁ χ₂ f α` by the inverse
components and cancel the two inverse laws. -/

/-- Total-category readout of inverse reindexing-comparison naturality. This avoids repeated
forgetful coercions in computations performed in the total category. -/
@[reassoc]
theorem Reindex.mapIso.inv.naturalityTotal
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv.1 =
      (Reindex.mapIso F χ₁ χ₂ f x).inv.1 ≫
        ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 := by
  exact congrArg (fun k ↦ k.1) (Reindex.mapIso.inv.naturality F χ₁ χ₂ f α)
/- Proof strategy: apply `congrArg (fun k ↦ k.1)` to
`Reindex.mapIso.inv.naturality F χ₁ χ₂ f α`. -/

/-- Naturality of the inverse reindexing comparison in the map presentation of the canonical
fiber pseudofunctors.

This orientation rewrites a comparison inverse followed by a mapped arrow, which is the useful
form in `pullHom` and conjugation calculations. -/
theorem Reindex.mapIso.inv.mapNaturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (χ₂.toPseudofunctor.map f.op.toLoc).toFunctor.map
          ((F.fiberFunctor U).map α) =
      (F.fiberFunctor V).map
          ((χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv := by
  exact (Reindex.mapIso.inv.naturality F χ₁ χ₂ f α).symm
/- Proof strategy: reverse `Reindex.mapIso.inv.naturality F χ₁ χ₂ f α`, then transport its
source and target reindexing functors across the two `toPseudofunctor.mapIso` bridges. -/

set_option backward.isDefEq.respectTransparency false in
/-- Applying a cartesian based functor to a reindexed fiber morphism is the reindexing of its
image conjugated by the two comparison isomorphisms. -/
theorem Reindex.mapIso.conjugation.fiber
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (F.fiberFunctor V).map ((f⁎[χ₁]).map α) =
      (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (f⁎[χ₂]).map ((F.fiberFunctor U).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom := by
  rw [Reindex.mapIso.hom.naturality F χ₁ χ₂ f α, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing the image of a fiber morphism is obtained by conjugating the image of its
reindexing by the forward comparison isomorphisms. -/
theorem Reindex.mapIso.conjugation.reindex
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (f⁎[χ₂]).map ((F.fiberFunctor U).map α) =
      (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (F.fiberFunctor V).map ((f⁎[χ₁]).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv := by
  rw [Reindex.mapIso.inv.naturality F χ₁ χ₂ f α, Iso.hom_inv_id_assoc]

/-- Total-category readout of `Reindex.mapIso.conjugation.fiber`. -/
theorem Reindex.mapIso.conjugation.totalFiber
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 =
      (Reindex.mapIso F χ₁ χ₂ f x).inv.1 ≫
        ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom.1 := by
  exact congrArg (fun k ↦ k.1) (Reindex.mapIso.conjugation.fiber F χ₁ χ₂ f α)

/-- Total-category readout of `Reindex.mapIso.conjugation.reindex`. -/
theorem Reindex.mapIso.conjugation.totalReindex
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 =
      (Reindex.mapIso F χ₁ χ₂ f x).hom.1 ≫
        ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv.1 := by
  exact congrArg (fun k ↦ k.1) (Reindex.mapIso.conjugation.reindex F χ₁ χ₂ f α)

end CartesianBasedFunctor

end CategoryTheory
