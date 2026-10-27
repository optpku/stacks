/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain.Basic

/-!
# Computations for left-domain maps of categorical pullbacks

Object and morphism formulas for left-domain change and its explicit inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Left-domain change applies `E` to the left endpoint object.

Proof strategy: project the explicit object formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.obj.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).fst = E.obj x.fst := rfl

/-- Left-domain change retains the right endpoint object.

Proof strategy: project the explicit object formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.obj.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).snd = x.snd := rfl

/-- Left-domain change retains the structural isomorphism.

Proof strategy: project the structural isomorphism of the explicit object formula of
`DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.obj.iso
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).iso = x.iso := by
  apply Iso.ext
  change (((CatCommSqOver.transform _).obj (DomainChange.Left.transform E F G)).obj
    (catCommSqOver (E ⋙ F) G)).iso.hom.app x = x.iso.hom
  rw [CatCommSqOver.transform_obj_obj_iso_hom_app]
  change 𝟙 _ ≫ x.iso.hom ≫ (𝟙 _ ≫ 𝟙 _) = x.iso.hom
  simp only [Category.id_comp, Category.comp_id]

/-- Left-domain change applies `E` to the left component of a morphism.

Proof strategy: project the explicit morphism formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.hom.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (E ⋙ F) ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.map E F G).map f).fst = E.map f.fst := rfl

/-- Left-domain change retains the right component of a morphism.

Proof strategy: project the explicit morphism formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.hom.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (E ⋙ F) ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.map E F G).map f).snd = f.snd := rfl

/-- Inverse left-domain change applies the inverse equivalence functor to the left endpoint. -/
@[simp]
theorem DomainChange.Left.inverse.obj.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).fst = E.inverse.obj x.fst := rfl

/-- Inverse left-domain change retains the right endpoint. -/
@[simp]
theorem DomainChange.Left.inverse.obj.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).snd = x.snd := rfl

/-- Inverse left-domain change transports the structural isomorphism by the counit of the
domain equivalence. -/
@[simp]
theorem DomainChange.Left.inverse.obj.iso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).iso =
      F.mapIso (E.counitIso.app x.fst) ≪≫ x.iso := by
  apply Iso.ext
  change (((CatCommSqOver.transform _).obj (DomainChange.Left.inverseTransform E F G)).obj
    (catCommSqOver F G)).iso.hom.app x =
      F.map (E.counitIso.hom.app x.fst) ≫ x.iso.hom
  rw [CatCommSqOver.transform_obj_obj_iso_hom_app]
  change (((𝟙 _ ≫ F.map (E.counitIso.hom.app x.fst)) ≫ 𝟙 _) ≫ 𝟙 _) ≫
      x.iso.hom ≫ (𝟙 _ ≫ 𝟙 _) = F.map (E.counitIso.hom.app x.fst) ≫ x.iso.hom
  simp only [Category.id_comp, Category.comp_id]

/-- Inverse left-domain change applies the inverse equivalence functor to the left component of
a morphism. -/
@[simp]
theorem DomainChange.Left.inverse.hom.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.inverse E F G).map f).fst = E.inverse.map f.fst := rfl

/-- Inverse left-domain change retains the right component of a morphism. -/
@[simp]
theorem DomainChange.Left.inverse.hom.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.inverse E F G).map f).snd = f.snd := rfl

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
