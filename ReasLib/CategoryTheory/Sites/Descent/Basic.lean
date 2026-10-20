/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Basic reusable API for descent data

This file extends the canonical mathlib owner `Pseudofunctor.DescentData` with the
hom-category operations most often needed by applications: evaluation at one member of the
covering family, objectwise evaluation of an isomorphism, and naturality of the transition
isomorphisms in both orientations.
-/

@[expose] public section

universe t uC vC uF vF

namespace CategoryTheory

open Opposite

namespace Pseudofunctor.DescentData

variable {C : Type uC} [Category.{vC} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}
variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- Evaluation of descent data and their morphisms at one member of the indexing family. -/
def eval (i : ι) :
    F.DescentData f ⥤ F.obj (LocallyDiscrete.mk (op (X i))) where
  obj D := D.obj i
  map φ := φ.hom i
  map_id D := id_hom D i
  map_comp φ ψ := comp_hom φ ψ i

/-- Evaluating a descent datum at `i` returns its `i`-th component object. -/
@[simp]
theorem eval_obj (i : ι) (D : F.DescentData f) :
    (eval i).obj D = D.obj i := sorry

/-- Evaluating a morphism of descent data at `i` returns its `i`-th component morphism. -/
@[simp]
theorem eval_map (i : ι) {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) :
    (eval i).map φ = φ.hom i := sorry

/-- Every component of an isomorphism-valued descent-data morphism is an isomorphism. -/
theorem isIso_hom {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    [IsIso φ] (i : ι) :
    IsIso (φ.hom i) := sorry

/-- A morphism of descent data is an isomorphism when each of its components is an
isomorphism. -/
theorem hom_isIso_of_components
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    (hφ : ∀ i, IsIso (φ.hom i)) :
    IsIso φ := sorry

/-- A morphism of descent data is an isomorphism exactly when all of its components are
isomorphisms. -/
theorem hom_isIso_iff
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) :
    IsIso φ ↔ ∀ i, IsIso (φ.hom i) := sorry

/-- The component at `i` of an isomorphism of descent data. -/
def isoApp {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i :=
  (eval i).mapIso e

/-- The forward map of `isoApp e i` is the `i`-th component of `e.hom`. -/
@[simp]
theorem isoApp_hom {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    (isoApp e i).hom = e.hom.hom i := sorry

/-- The inverse map of `isoApp e i` is the `i`-th component of `e.inv`. -/
@[simp]
theorem isoApp_inv {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    (isoApp e i).inv = e.inv.hom i := sorry

/-- The inverses of a coherent family of component isomorphisms satisfy the reverse
descent-data compatibility. -/
theorem isoMkOfComponents_inv_comm
    {D₁ D₂ : F.DescentData f} (e : ∀ i, D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
      (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom q f₁ f₂ hf₁ hf₂ =
        D₁.hom q f₁ f₂ hf₁ hf₂ ≫
          (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom) :
    ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
      (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ =
        D₂.hom q f₁ f₂ hf₁ hf₂ ≫
          (F.map f₂.op.toLoc).toFunctor.map (e i₂).inv := sorry

/-- Construct an isomorphism of descent data from component isomorphisms and an explicit
compatibility theorem.

Unlike mathlib's `Pseudofunctor.DescentData.isoMk`, this constructor exposes the compatibility
as an ordinary argument instead of an `autoParam`, which is useful when the coherence is a
named reusable theorem. -/
def isoMkOfComponents
    {D₁ D₂ : F.DescentData f} (e : ∀ i, D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
      (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom q f₁ f₂ hf₁ hf₂ =
        D₁.hom q f₁ f₂ hf₁ hf₂ ≫
          (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom) :
    D₁ ≅ D₂ where
  hom :=
    { hom := fun i ↦ (e i).hom
      comm := comm }
  inv :=
    { hom := fun i ↦ (e i).inv
      comm := isoMkOfComponents_inv_comm e comm }
  hom_inv_id := hom_ext (fun i ↦ (e i).hom_inv_id)
  inv_hom_id := hom_ext (fun i ↦ (e i).inv_hom_id)

/-- The transition isomorphism from a restriction leg to itself is the identity isomorphism. -/
@[simp]
theorem iso_refl
    (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄
    (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    D.iso q g g hg hg = Iso.refl _ := sorry

/-- Reversing the two restriction legs reverses the transition isomorphism. -/
@[simp]
theorem iso_symm
    (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (D.iso q f₁ f₂ hf₁ hf₂).symm =
      D.iso q f₂ f₁ hf₂ hf₁ := sorry

/-- Transition isomorphisms compose along three restriction legs over the same base map. -/
theorem iso_trans
    (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (hf₃ : f₃ ≫ f i₃ = q) :
    D.iso q f₁ f₂ hf₁ hf₂ ≪≫ D.iso q f₂ f₃ hf₂ hf₃ =
      D.iso q f₁ f₃ hf₁ hf₃ := sorry

/-- The forward transition isomorphisms of descent data are natural in a morphism of descent
data. -/
theorem iso_hom_naturality
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫
        (D₂.iso q f₁ f₂ hf₁ hf₂).hom =
      (D₁.iso q f₁ f₂ hf₁ hf₂).hom ≫
        (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := sorry

/-- The inverse transition isomorphisms of descent data are natural in a morphism of descent
data. This orientation is convenient when a transition inverse occurs after a mapped
component. -/
theorem iso_inv_naturality
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) ≫
        (D₂.iso q f₁ f₂ hf₁ hf₂).inv =
      (D₁.iso q f₁ f₂ hf₁ hf₂).inv ≫
        (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) := sorry

end Pseudofunctor.DescentData

namespace Pseudofunctor.IsStackFor

variable {C : Type uC} [Category.{vC} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}
variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- Effective descent for the presieve generated by an arrow family makes the corresponding
descent-data functor essentially surjective.  This is the arrow-family form of mathlib's
`IsStackFor.essSurj`, avoiding a downstream local `IsEquivalence` instance. -/
theorem essSurj_ofArrows
    (h : F.IsStackFor (Presieve.ofArrows X f)) :
    (F.toDescentData f).EssSurj := sorry

end Pseudofunctor.IsStackFor

end CategoryTheory
