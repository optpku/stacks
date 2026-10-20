/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Localization.HomEquiv
public import Mathlib.CategoryTheory.Comma.Arrow

@[expose] public section

noncomputable section

namespace CategoryTheory.Localization

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]

/-- The reverse edge of a morphism inverted by a localization, transported to that localization. -/
def formalInverse {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj Y ⟶ L.obj X :=
  homEquiv W W.Q L (Construction.wInv f hf)

/-- A localized morphism and its transported reverse edge are mutually inverse. -/
theorem formalIso_laws {X Y : C} (f : X ⟶ Y) (hf : W f) :
    L.map f ≫ formalInverse W L f hf = 𝟙 _ ∧
      formalInverse W L f hf ≫ L.map f = 𝟙 _ :=
  sorry

/-- The isomorphism associated to a specified inverted morphism, using its formal reverse edge. -/
def formalIso {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y where
  hom := L.map f
  inv := formalInverse W L f hf
  hom_inv_id := (formalIso_laws W L f hf).1
  inv_hom_id := (formalIso_laws W L f hf).2

omit [L.IsLocalization W] in
/-- An arrow representing a specified target morphism under an essentially surjective arrow functor. -/
def arrowRepresentative (L : C ⥤ D) [L.mapArrow.EssSurj] {X Y : D} (f : X ⟶ Y) :
    Arrow C :=
  L.mapArrow.objPreimage (Arrow.mk f)

omit [L.IsLocalization W] in
/-- The arrow presentation identifies the representative with the specified target morphism. -/
def arrowRepresentativeIso (L : C ⥤ D) [L.mapArrow.EssSurj] {X Y : D} (f : X ⟶ Y) :
    L.mapArrow.obj (arrowRepresentative L f) ≅ Arrow.mk f :=
  L.mapArrow.objObjPreimageIso (Arrow.mk f)

/-- Formal inversion of an inverted arrow representative, transported along its arrow presentation. -/
def formalIsoOfArrowRepresentative [L.mapArrow.EssSurj] {X Y : D} (f : X ⟶ Y)
    (hf : W (arrowRepresentative L f).hom) : X ≅ Y :=
  (Arrow.leftFunc.mapIso (arrowRepresentativeIso L f)).symm ≪≫
    formalIso W L (arrowRepresentative L f).hom hf ≪≫
    Arrow.rightFunc.mapIso (arrowRepresentativeIso L f)

/-- Formal inversion of an arrow representative retains the specified forward morphism. -/
theorem formalIsoOfArrowRepresentative_hom [L.mapArrow.EssSurj] {X Y : D} (f : X ⟶ Y)
    (hf : W (arrowRepresentative L f).hom) :
    (formalIsoOfArrowRepresentative W L f hf).hom = f :=
  (Arrow.iso_w (arrowRepresentativeIso L f)).symm

end CategoryTheory.Localization

