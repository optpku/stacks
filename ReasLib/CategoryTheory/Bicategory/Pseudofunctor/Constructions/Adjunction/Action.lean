/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Adjunction.Mapping

/-!
# Pseudofunctorial action on bicategorical adjunctions

Assembly and computation rules for the pseudofunctor induced on bicategories
of adjunctions.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
namespace Pseudofunctor

universe wC vC uC wD vD uD

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

section MapAdjunctionsImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The implementation-level prelax action of a pseudofunctor on adjunctions and mate
transformations. -/
private def mapAdj.prelax (F : B ⥤ᵖ C) :
    PrelaxFunctor (Bicategory.Adj B) (Bicategory.Adj C) :=
  PrelaxFunctor.mkOfHomFunctors
    (mapAdj.object F) (mapAdj.hom.functor F)

/-- The induced action on adjunctions preserves left whiskering. -/
private theorem mapAdj.map₂.whiskerLeft (F : B ⥤ᵖ C) :
    ∀ {a b c : Bicategory.Adj B}
      (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      (mapAdj.prelax F).map₂ (f ◁ η) =
        (mapAdj.mapCompIso F f g).hom ≫
          (mapAdj.prelax F).map f ◁
            (mapAdj.prelax F).map₂ η ≫
          (mapAdj.mapCompIso F f h).inv := by
  intro a b c f g h η
  apply Bicategory.Adj.hom₂_ext
  exact F.map₂_whisker_left f.l η.τl

/-- The induced action on adjunctions preserves right whiskering. -/
private theorem mapAdj.map₂.whiskerRight (F : B ⥤ᵖ C) :
    ∀ {a b c : Bicategory.Adj B}
      {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      (mapAdj.prelax F).map₂ (η ▷ h) =
        (mapAdj.mapCompIso F f h).hom ≫
          (mapAdj.prelax F).map₂ η ▷
            (mapAdj.prelax F).map h ≫
          (mapAdj.mapCompIso F g h).inv := by
  intro a b c f g η h
  apply Bicategory.Adj.hom₂_ext
  exact F.map₂_whisker_right η.τl h.l

/-- The induced action on adjunctions preserves the associator modulo its canonical
composition comparisons. -/
private theorem mapAdj.map₂.associator (F : B ⥤ᵖ C) :
    ∀ {a b c d : Bicategory.Adj B}
      (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (mapAdj.prelax F).map₂ (α_ f g h).hom =
        (mapAdj.mapCompIso F (f ≫ g) h).hom ≫
          (mapAdj.mapCompIso F f g).hom ▷
            (mapAdj.prelax F).map h ≫
          (α_ ((mapAdj.prelax F).map f)
            ((mapAdj.prelax F).map g)
            ((mapAdj.prelax F).map h)).hom ≫
          (mapAdj.prelax F).map f ◁
            (mapAdj.mapCompIso F g h).inv ≫
          (mapAdj.mapCompIso F f (g ≫ h)).inv := by
  intro a b c d f g h
  apply Bicategory.Adj.hom₂_ext
  exact F.map₂_associator f.l g.l h.l

/-- The induced action on adjunctions preserves the left unitor modulo its canonical identity
and composition comparisons. -/
private theorem mapAdj.map₂.leftUnitor (F : B ⥤ᵖ C) :
    ∀ {a b : Bicategory.Adj B} (f : a ⟶ b),
      (mapAdj.prelax F).map₂ (λ_ f).hom =
        (mapAdj.mapCompIso F (𝟙 a) f).hom ≫
          (mapAdj.mapIdIso F a).hom ▷
            (mapAdj.prelax F).map f ≫
          (λ_ ((mapAdj.prelax F).map f)).hom := by
  intro a b f
  apply Bicategory.Adj.hom₂_ext
  exact F.map₂_left_unitor f.l

/-- The induced action on adjunctions preserves the right unitor modulo its canonical identity
and composition comparisons. -/
private theorem mapAdj.map₂.rightUnitor (F : B ⥤ᵖ C) :
    ∀ {a b : Bicategory.Adj B} (f : a ⟶ b),
      (mapAdj.prelax F).map₂ (ρ_ f).hom =
        (mapAdj.mapCompIso F f (𝟙 b)).hom ≫
          (mapAdj.prelax F).map f ◁
            (mapAdj.mapIdIso F b).hom ≫
          (ρ_ ((mapAdj.prelax F).map f)).hom := by
  intro a b f
  apply Bicategory.Adj.hom₂_ext
  exact F.map₂_right_unitor f.l

/-- Extensionality for prelax functors, including their dependent morphism actions. -/
private theorem prelax_ext (F G : PrelaxFunctor B C)
    (ho : F.obj = G.obj) (hm : HEq (@F.map) (@G.map))
    (h₂ : HEq (@F.map₂) (@G.map₂)) : F = G := by
  rcases F with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
  rcases G with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
  cases ho
  cases hm
  cases h₂
  rfl

/-- Extensionality for pseudofunctors once all their data agree. -/
private theorem pseudofunctor_ext (F G : B ⥤ᵖ C)
    (hp : F.toPrelaxFunctor = G.toPrelaxFunctor)
    (hi : HEq F.mapId G.mapId) (hc : HEq (@F.mapComp) (@G.mapComp)) : F = G := by
  cases F
  cases G
  cases hp
  cases hi
  cases hc
  rfl

/-- Isomorphisms with equal endpoints agree heterogeneously when their forward cells do. -/
private theorem iso_hext {E : Type*} [Category E] {a b a' b' : E}
    (e : a ≅ b) (e' : a' ≅ b') (ha : a = a') (hb : b = b')
    (hh : HEq e.hom e'.hom) : HEq e e' := by
  cases ha
  cases hb
  exact heq_of_eq (Iso.ext (eq_of_heq hh))

/-- A mate pair with transported endpoints is determined by its left component. -/
private theorem hom₂_hext {a b : Bicategory.Adj B} {f g f' g' : a ⟶ b}
    (η : f ⟶ g) (θ : f' ⟶ g') (hf : f = f') (hg : g = g')
    (hl : HEq η.τl θ.τl) : HEq η θ := by
  cases hf
  cases hg
  exact heq_of_eq (Bicategory.Adj.hom₂_ext (eq_of_heq hl))

end Implementation

/-- The pseudofunctor induced on bicategories of adjunctions.

It sends an adjunction to its canonical image under `F` and sends a mate transformation by
mapping both mate components. Its identity and composition comparisons are the mate pairs
formed from `F.mapId` and `F.mapComp`. -/
@[stacks 0040 "pseudofunctorial action on bicategorical adjunctions"]
def mapAdj (F : B ⥤ᵖ C) :
    Bicategory.Adj B ⥤ᵖ Bicategory.Adj C where
  toPrelaxFunctor := Implementation.mapAdj.prelax F
  mapId := mapAdj.mapIdIso F
  mapComp := mapAdj.mapCompIso F
  map₂_whisker_left := Implementation.mapAdj.map₂.whiskerLeft F
  map₂_whisker_right := Implementation.mapAdj.map₂.whiskerRight F
  map₂_associator := Implementation.mapAdj.map₂.associator F
  map₂_left_unitor := Implementation.mapAdj.map₂.leftUnitor F
  map₂_right_unitor := Implementation.mapAdj.map₂.rightUnitor F

/-- The object action of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.obj
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    F.mapAdj.obj a = mapAdj.object F a := by
  rfl

/-- The ambient object underlying the image of an object of `Adj B`. -/
@[simp]
theorem mapAdj.obj.carrier
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.obj a).obj = F.obj a.obj := by
  rfl

/-- The `1`-morphism action of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.map
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    F.mapAdj.map f = mapAdj.hom F f := by
  rfl

/-- The left adjoint underlying the image of an adjunction. -/
@[simp]
theorem mapAdj.map.l
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (F.mapAdj.map f).l = F.map f.l := by
  rfl

/-- The right adjoint underlying the image of an adjunction. -/
@[simp]
theorem mapAdj.map.r
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (F.mapAdj.map f).r = F.map f.r := by
  rfl

/-- The adjunction underlying the image of an `Adj`-morphism. -/
@[simp]
theorem mapAdj.map.adj
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (F.mapAdj.map f).adj =
      F.mapAdjunction f.adj := by
  rfl

/-- The `2`-morphism action of the induced pseudofunctor on mate transformations. -/
@[simp]
theorem mapAdj.map₂
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    F.mapAdj.map₂ η = mapAdj.hom₂ F η := by
  rfl

/-- The left-adjoint component of the image of a mate transformation. -/
@[simp]
theorem mapAdj.map₂.τl
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (F.mapAdj.map₂ η).τl = F.map₂ η.τl := by
  rfl

/-- The right-adjoint component of the image of a mate transformation. -/
@[simp]
theorem mapAdj.map₂.τr
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (F.mapAdj.map₂ η).τr = F.map₂ η.τr := by
  rfl

/-- The hom-category action of the induced pseudofunctor is the canonical mate-mapping
functor. -/
@[simp]
theorem mapAdj.mapFunctor
    (F : B ⥤ᵖ C) (a b : Bicategory.Adj B) :
    F.mapAdj.mapFunctor a b =
      mapAdj.hom.functor F a b := by
  rfl

/-- The identity comparison of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.mapId
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    F.mapAdj.mapId a = mapAdj.mapIdIso F a := by
  rfl

/-- The forward left-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.hom.τl
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).hom.τl =
      (F.mapId a.obj).hom := by
  rfl

/-- The forward right-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.hom.τr
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).hom.τr =
      (F.mapId a.obj).inv := by
  rfl

/-- The inverse left-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.inv.τl
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).inv.τl =
      (F.mapId a.obj).inv := by
  rfl

/-- The inverse right-adjoint component of the induced identity comparison. -/
@[simp]
theorem mapAdj.mapId.inv.τr
    (F : B ⥤ᵖ C) (a : Bicategory.Adj B) :
    (F.mapAdj.mapId a).inv.τr =
      (F.mapId a.obj).hom := by
  rfl

/-- The composition comparison of the induced pseudofunctor on adjunctions. -/
@[simp]
theorem mapAdj.mapComp
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    F.mapAdj.mapComp f g =
      mapAdj.mapCompIso F f g := by
  rfl

/-- The forward left-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.hom.τl
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).hom.τl =
      (F.mapComp f.l g.l).hom := by
  rfl

/-- The forward right-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.hom.τr
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).hom.τr =
      (F.mapComp g.r f.r).inv := by
  rfl

/-- The inverse left-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.inv.τl
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).inv.τl =
      (F.mapComp f.l g.l).inv := by
  rfl

/-- The inverse right-adjoint component of the induced composition comparison. -/
@[simp]
theorem mapAdj.mapComp.inv.τr
    (F : B ⥤ᵖ C) {a b c : Bicategory.Adj B}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapAdj.mapComp f g).inv.τr =
      (F.mapComp g.r f.r).hom := by
  rfl

/-- Forgetting to left adjoints after applying `mapAdj` agrees with first forgetting the
adjunctions and then applying the original pseudofunctor. -/
@[simp]
theorem mapAdj.comp_forget₁ (F : B ⥤ᵖ C) :
    F.mapAdj.comp (Bicategory.Adj.forget₁ (B := C)) =
      (Bicategory.Adj.forget₁ (B := B)).comp F := by
  dsimp only [Pseudofunctor.comp]
  congr 1
  · funext a
    apply Iso.ext
    change (F.mapId a.obj).hom ≫ 𝟙 _ = F.map₂ (𝟙 _) ≫ (F.mapId a.obj).hom
    simp only [Category.comp_id, Category.id_comp, PrelaxFunctor.map₂_id]
  · funext a b c f g
    apply Iso.ext
    change (F.mapComp f.l g.l).hom ≫ 𝟙 _ = F.map₂ (𝟙 _) ≫ (F.mapComp f.l g.l).hom
    simp only [Category.comp_id, Category.id_comp, PrelaxFunctor.map₂_id]

/-- Taking the left-adjoint isomorphism after mapping an isomorphism of adjunctions agrees
with mapping its original left-adjoint isomorphism. -/
@[simp]
theorem mapAdj.map₂Iso.lIso
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (e : f ≅ g) :
    Bicategory.Adj.lIso (F.mapAdj.map₂Iso e) =
      F.map₂Iso (Bicategory.Adj.lIso e) := by
  rfl

/-- Taking the right-adjoint isomorphism after mapping an isomorphism of adjunctions agrees
with mapping its original right-adjoint isomorphism. -/
@[simp]
theorem mapAdj.map₂Iso.rIso
    (F : B ⥤ᵖ C) {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (e : f ≅ g) :
    Bicategory.Adj.rIso (F.mapAdj.map₂Iso e) =
      F.map₂Iso (Bicategory.Adj.rIso e) := by
  rfl

/-- The identity pseudofunctor induces the identity pseudofunctor on the bicategory of
adjunctions. -/
@[simp]
theorem mapAdj.id :
    (Pseudofunctor.id B).mapAdj =
      Pseudofunctor.id (Bicategory.Adj B) := by
  have h {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r) :
      (Pseudofunctor.id B).mapAdjunction adj = adj := by
    apply Adjunction.ext
    · change 𝟙 _ ≫ adj.unit ≫ 𝟙 _ = adj.unit
      simp only [Category.comp_id, Category.id_comp]
    · change 𝟙 _ ≫ adj.counit ≫ 𝟙 _ = adj.counit
      simp only [Category.comp_id, Category.id_comp]
  have hm {a b : Bicategory.Adj B} (f : a ⟶ b) :
      mapAdj.hom (Pseudofunctor.id B) f = f := by
    cases f
    dsimp only [mapAdj.hom]
    rw [h]
    rfl
  apply Implementation.pseudofunctor_ext
  · apply Implementation.prelax_ext
    · rfl
    · exact heq_of_eq (funext fun a ↦ funext fun b ↦ funext fun f ↦ hm f)
    · iterate 5
        apply Function.hfunext rfl
        intro x y hxy
        cases hxy
      exact Implementation.hom₂_hext _ _ (hm _) (hm _) (HEq.refl _)
  · apply Function.hfunext rfl
    intro a a' ha
    cases ha
    apply Implementation.iso_hext _ _ (hm _) rfl
    exact Implementation.hom₂_hext _ _ (hm _) rfl (HEq.refl _)
  · iterate 5
      apply Function.hfunext rfl
      intro x y hxy
      cases hxy
    apply Implementation.iso_hext _ _ (hm _) (congrArg₂ (fun f g ↦ f ≫ g) (hm _) (hm _))
    exact Implementation.hom₂_hext _ _ (hm _)
      (congrArg₂ (fun f g ↦ f ≫ g) (hm _) (hm _)) (HEq.refl _)

section MapAdjComposition

variable {D : Type uD} [Bicategory.{wD, vD} D]

/-- The action on adjunctions induced by a composite pseudofunctor agrees with the composite
of the two induced actions. -/
@[simp]
theorem mapAdj.comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) :
    (F.comp G).mapAdj =
      F.mapAdj.comp G.mapAdj := by
  have h {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r) :
      (F.comp G).mapAdjunction adj = G.mapAdjunction (F.mapAdjunction adj) := by
    apply Adjunction.ext
    · change ((G.mapId (F.obj a)).inv ≫ G.map₂ (F.mapId a).inv) ≫
          G.map₂ (F.map₂ adj.unit) ≫ G.map₂ (F.mapComp l r).hom ≫
            (G.mapComp (F.map l) (F.map r)).hom = _
      simp only [Pseudofunctor.mapAdjunction_unit, PrelaxFunctor.map₂_comp, Category.assoc]
    · change ((G.mapComp (F.map r) (F.map l)).inv ≫ G.map₂ (F.mapComp r l).inv) ≫
          G.map₂ (F.map₂ adj.counit) ≫ G.map₂ (F.mapId b).hom ≫ (G.mapId (F.obj b)).hom = _
      simp only [Pseudofunctor.mapAdjunction_counit, PrelaxFunctor.map₂_comp, Category.assoc]
  have hm {a b : Bicategory.Adj B} (f : a ⟶ b) :
      mapAdj.hom (F.comp G) f = mapAdj.hom G (mapAdj.hom F f) := by
    dsimp only [mapAdj.hom]
    rw [h]
    rfl
  apply Implementation.pseudofunctor_ext
  · apply Implementation.prelax_ext
    · rfl
    · exact heq_of_eq (funext fun a ↦ funext fun b ↦ funext fun f ↦ hm f)
    · iterate 5
        apply Function.hfunext rfl
        intro x y hxy
        cases hxy
      exact Implementation.hom₂_hext _ _ (hm _) (hm _) (HEq.refl _)
  · apply Function.hfunext rfl
    intro a a' ha
    cases ha
    apply Implementation.iso_hext _ _ (hm _) rfl
    exact Implementation.hom₂_hext _ _ (hm _) rfl (HEq.refl _)
  · iterate 5
      apply Function.hfunext rfl
      intro x y hxy
      cases hxy
    apply Implementation.iso_hext _ _ (hm _) (congrArg₂ (fun f g ↦ f ≫ g) (hm _) (hm _))
    exact Implementation.hom₂_hext _ _ (hm _)
      (congrArg₂ (fun f g ↦ f ≫ g) (hm _) (hm _)) (HEq.refl _)


end MapAdjComposition

/- Data audit (mathlib 4.32): `mapAdj` stores mapped objects, both adjoint `1`-morphisms,
both mate components, and both directions of the identity and composition comparisons
explicitly. Its `sorryAx` is confined to Prop-valued mate and pseudofunctor coherence fields;
no adjunction, mate component, or comparison cell is selected from an existence witness. -/

end MapAdjunctionsImplementation

end Pseudofunctor

end CategoryTheory
