/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Descent in slice categories

This module provides the contravariant pseudofunctor of slice categories and the canonical
essential-image formulation of effective descent.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

universe u v w

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

/-- The two composite arrows underlying associativity give the same slice pullback functor. -/
theorem pullbackAssocFunctorEq
    {X₀ X₁ X₂ X₃ : Cᵒᵖ} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (pullback (h.unop ≫ (f ≫ g).unop)).toCatHom =
      (pullback ((g ≫ h).unop ≫ f.unop)).toCatHom := by
  ext
  simp

/-- Pullback along the composite with an identity on the source agrees with pullback. -/
theorem pullbackLeftUnitFunctorEq {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (pullback (f.unop ≫ (𝟙 X).unop)).toCatHom = (pullback f.unop).toCatHom := by
  ext
  simp

/-- Pullback along the composite with an identity on the target agrees with pullback. -/
theorem pullbackRightUnitFunctorEq {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (pullback ((𝟙 Y).unop ≫ f.unop)).toCatHom = (pullback f.unop).toCatHom := by
  ext
  simp

/-- The associativity coherence for repeated pullback between slice categories. -/
theorem pseudofunctorMap₂Associator
    {X₀ X₁ X₂ X₃ : Cᵒᵖ} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (pullbackComp h.unop (f ≫ g).unop)).hom ≫
        (Cat.Hom.isoMk (pullbackComp g.unop f.unop)).hom ▷
          (pullback h.unop).toCatHom ≫
      (α_ (pullback f.unop).toCatHom (pullback g.unop).toCatHom
        (pullback h.unop).toCatHom).hom ≫
      (pullback f.unop).toCatHom ◁
        (Cat.Hom.isoMk (pullbackComp h.unop g.unop)).inv ≫
      (Cat.Hom.isoMk (pullbackComp (g ≫ h).unop f.unop)).inv =
        eqToHom (pullbackAssocFunctorEq f g h) := sorry

/-- The left-unit coherence for pullback between slice categories. -/
theorem pseudofunctorMap₂LeftUnitor {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (pullbackComp f.unop (𝟙 X).unop)).hom ≫
        (Cat.Hom.isoMk pullbackId).hom ▷ (pullback f.unop).toCatHom ≫
      (λ_ (pullback f.unop).toCatHom).hom = eqToHom (pullbackLeftUnitFunctorEq f) := sorry

/-- The right-unit coherence for pullback between slice categories. -/
theorem pseudofunctorMap₂RightUnitor {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (pullbackComp (𝟙 Y).unop f.unop)).hom ≫
        (pullback f.unop).toCatHom ◁ (Cat.Hom.isoMk pullbackId).hom ≫
      (ρ_ (pullback f.unop).toCatHom).hom = eqToHom (pullbackRightUnitFunctorEq f) := sorry

/-- The contravariant pseudofunctor sending an object to its slice category and a morphism to
pullback along that morphism. -/
noncomputable def pseudofunctor : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v, max u v} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Over X.unop))
    (fun f ↦ (pullback f.unop).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk pullbackId)
    (fun f g ↦ Cat.Hom.isoMk (pullbackComp g.unop f.unop))
    pseudofunctorMap₂Associator pseudofunctorMap₂LeftUnitor pseudofunctorMap₂RightUnitor

/-- The fibre of `Over.pseudofunctor` at `X` is the slice category `Over X`. -/
theorem pseudofunctor_obj (X : C) :
    pseudofunctor.obj (.mk (.op X)) = Cat.of (Over X) := sorry

/-- The action of `Over.pseudofunctor` on `f` is pullback along `f`. -/
theorem pseudofunctor_map {X Y : C} (f : X ⟶ Y) :
    (pseudofunctor.map f.op.toLoc).toFunctor = pullback f := sorry

variable {I : Type w} {S : C} (X : I → C) (p : ∀ i, X i ⟶ S)

/-- The category of descent data for a family of morphisms into `S`. -/
abbrev DescentData := pseudofunctor.DescentData p

namespace DescentData

/-- A slice descent datum is effective when it is in the essential image of the canonical
functor from the slice over the base. -/
abbrev IsEffective (D : pseudofunctor.DescentData p) : Prop :=
  (pseudofunctor.toDescentData p).essImage D

/-- Effectivity is equivalently the existence of a slice object whose canonical descent datum
is isomorphic to the given datum. -/
theorem isEffective_iff {D : pseudofunctor.DescentData p} :
    IsEffective X p D ↔ ∃ T : Over S,
      Nonempty ((pseudofunctor.toDescentData p).obj T ≅ D) := sorry

/-- Pulling an object of `Over S` back along every `p i` gives canonical descent data. -/
noncomputable def ofObj (T : Over S) : DescentData X p :=
  (pseudofunctor.toDescentData p).obj T

/-- The component of canonical descent data is the corresponding slice pullback. -/
theorem ofObj_obj (T : Over S) (i : I) :
    (ofObj X p T).obj i = (Over.pullback (p i)).obj T := sorry

/-- The chosen pairwise- and triple-pullback presentation of descent data. -/
abbrev Chosen
    (sq : ∀ i j, ChosenPullback (p i) (p j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :=
  pseudofunctor.DescentData' sq sq₃

namespace Chosen

variable (sq : ∀ i j, ChosenPullback (p i) (p j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

/-- Invertible pairwise comparisons satisfying the triple-overlap cocycle satisfy normalization. -/
theorem ofIso_self
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : I) :
    Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
      (p i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := sorry

/-- A chosen presentation is constructed from component objects, pairwise isomorphisms, and their
triple-overlap cocycle. -/
def ofIso
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃) :
    Chosen X p sq sq₃ where
  obj := V
  hom i j := (φ i j).hom
  pullHom'_hom_self i := ofIso_self X p sq sq₃ V φ hφ i
  pullHom'_hom_comp := hφ

/-- The component object of a chosen presentation built by `ofIso` is the supplied object. -/
theorem ofIso_obj
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : I) : (ofIso X p sq sq₃ V φ hφ).obj i = V i := sorry

/-- The pairwise comparison map of a chosen presentation is the supplied forward map. -/
theorem ofIso_hom
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i j : I) : (ofIso X p sq sq₃ V φ hφ).hom i j = (φ i j).hom := sorry

/-- The pairwise comparison morphism of chosen descent data, with inverse obtained by
pulling the reverse comparison back along the swapped projections of the chosen overlap. -/
noncomputable def iso (D : Chosen X p sq sq₃) (i j : I) :
    (pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (D.obj i) ≅
      (pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (D.obj j) where
  hom := D.hom i j
  inv := Pseudofunctor.DescentData'.pullHom' D.hom
    (sq i j).p (sq i j).p₂ (sq i j).p₁
  hom_inv_id := by
    rw [← D.pullHom'_eq_hom i j]
    simpa using
      (Pseudofunctor.DescentData'.comp_pullHom' D (sq i j).p
        (sq i j).p₁ (sq i j).p₂ (sq i j).p₁)
  inv_hom_id := by
    rw [← D.pullHom'_eq_hom i j]
    simpa using
      (Pseudofunctor.DescentData'.comp_pullHom' D (sq i j).p
        (sq i j).p₂ (sq i j).p₁ (sq i j).p₂)

/-- The forward map of `iso D i j` is the pairwise comparison map of `D`. -/
theorem iso_hom (D : Chosen X p sq sq₃) (i j : I) :
    (iso X p sq sq₃ D i j).hom = D.hom i j := rfl

/-- The inverse comparison uses the reverse descent map on the same overlap, with its two
projections exchanged. -/
theorem iso_inv (D : Chosen X p sq sq₃) (i j : I) :
    (iso X p sq sq₃ D i j).inv =
      Pseudofunctor.DescentData'.pullHom' D.hom
        (sq i j).p (sq i j).p₂ (sq i j).p₁ := rfl

/-- The pairwise comparison isomorphisms satisfy the triple-overlap cocycle condition. -/
theorem cocycle (D : Chosen X p sq sq₃) (i j k : I) :
    Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso X p sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso X p sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso X p sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃ :=
  D.pullHom'_hom_comp i j k

/-- A morphism of chosen descent data commutes with every pairwise comparison isomorphism. -/
theorem hom_comm {D E : Chosen X p sq sq₃} (ψ : D ⟶ E) (i j : I) :
    (pseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.map (ψ.hom i) ≫
        (iso X p sq sq₃ E i j).hom =
      (iso X p sq sq₃ D i j).hom ≫
        (pseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.map (ψ.hom j) :=
  ψ.comm i j

/-- The canonical equivalence from the chosen-overlap presentation to canonical descent data. -/
noncomputable abbrev equivalence : Chosen X p sq sq₃ ≌ DescentData X p :=
  Pseudofunctor.DescentData'.descentDataEquivalence pseudofunctor sq sq₃

/-- The chosen-to-canonical equivalence retains every component object. -/
theorem equivalence_functor_obj_obj (D : Chosen X p sq sq₃) (i : I) :
    ((equivalence X p sq sq₃).functor.obj D).obj i = D.obj i := sorry

/-- The chosen-to-canonical equivalence retains every component of a descent morphism. -/
theorem equivalence_functor_map_hom {D E : Chosen X p sq sq₃}
    (ψ : D ⟶ E) (i : I) :
    ((equivalence X p sq sq₃).functor.map ψ).hom i = ψ.hom i := sorry

end Chosen

end DescentData

end CategoryTheory.Over
