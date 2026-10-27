/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.RightDomain.Basic

/-!
# Computations for right-domain maps of categorical pullbacks

Object and morphism formulas for right-domain change and its explicit inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Right-domain change retains the left endpoint object.

Proof strategy: project the explicit object formula of `DomainChange.Right.map`. -/
@[simp]
theorem DomainChange.Right.map.obj.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ (E ⋙ G)) :
    ((DomainChange.Right.map E F G).obj x).fst = x.fst := rfl

/-- Right-domain change applies `E` to the right endpoint object.

Proof strategy: project the explicit object formula of `DomainChange.Right.map`. -/
@[simp]
theorem DomainChange.Right.map.obj.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ (E ⋙ G)) :
    ((DomainChange.Right.map E F G).obj x).snd = E.obj x.snd := rfl

/-- Right-domain change retains the structural isomorphism.

Proof strategy: project the structural isomorphism of the explicit object formula of
`DomainChange.Right.map`. -/
@[simp]
theorem DomainChange.Right.map.obj.iso
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ (E ⋙ G)) :
    ((DomainChange.Right.map E F G).obj x).iso = x.iso := by
  apply Iso.ext
  change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ ≫ x.iso.hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = x.iso.hom
  simp only [Category.id_comp, Category.comp_id]

/-- Right-domain change retains the left component of a morphism.

Proof strategy: project the explicit morphism formula of `DomainChange.Right.map`. -/
@[simp]
theorem DomainChange.Right.map.hom.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ (E ⋙ G)} (f : x ⟶ y) :
    ((DomainChange.Right.map E F G).map f).fst = f.fst := rfl

/-- Right-domain change applies `E` to the right component of a morphism.

Proof strategy: project the explicit morphism formula of `DomainChange.Right.map`. -/
@[simp]
theorem DomainChange.Right.map.hom.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ (E ⋙ G)} (f : x ⟶ y) :
    ((DomainChange.Right.map E F G).map f).snd = E.map f.snd := rfl

/-- Inverse right-domain change retains the left endpoint. -/
@[simp]
theorem DomainChange.Right.inverse.obj.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Right.inverse E F G).obj x).fst = x.fst := rfl

/-- Inverse right-domain change applies the inverse equivalence functor to the right endpoint. -/
@[simp]
theorem DomainChange.Right.inverse.obj.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Right.inverse E F G).obj x).snd = E.inverse.obj x.snd := rfl

/-- Inverse right-domain change transports the structural isomorphism by the inverse counit of
the domain equivalence. -/
@[simp]
theorem DomainChange.Right.inverse.obj.iso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Right.inverse E F G).obj x).iso =
      x.iso ≪≫ G.mapIso (E.counitIso.app x.snd).symm := by
  apply Iso.ext
  change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ ≫ x.iso.hom ≫ 𝟙 _ ≫
      (𝟙 _ ≫ 𝟙 _ ≫ G.map (E.counitIso.inv.app x.snd) ≫ 𝟙 _) ≫ 𝟙 _ =
    x.iso.hom ≫ G.map (E.counitIso.inv.app x.snd)
  simp only [Category.id_comp, Category.comp_id]

/-- Inverse right-domain change retains the left component of a morphism. -/
@[simp]
theorem DomainChange.Right.inverse.hom.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Right.inverse E F G).map f).fst = f.fst := rfl

/-- Inverse right-domain change applies the inverse equivalence functor to the right component of
a morphism. -/
@[simp]
theorem DomainChange.Right.inverse.hom.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Right.inverse E F G).map f).snd = E.inverse.map f.snd := rfl

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
