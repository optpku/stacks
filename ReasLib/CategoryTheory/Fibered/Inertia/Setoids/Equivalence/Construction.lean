/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-! # Inertia equivalences for categories fibred in setoids -/

@[expose] public section

universe u v vS w uY vY

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace BasedCategory.RelativeInertia.forget

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vS, max w vS} C} {Y : BasedCategory.{vY, uY} C}

/-- The identity arrow intertwines a relative-inertia automorphism with the neutral automorphism. -/
theorem unitIsoApp.naturality (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    A.aut.hom ≫ 𝟙 A.obj =
      𝟙 A.obj ≫
        (CategoryTheory.RelativeInertia.identitySection.obj F.toFunctor A.obj).aut.hom := sorry

/-- The explicit objectwise unit isomorphism in setoid fibres. -/
@[stacks 04Z3 "relative-inertia unit component in setoid fibres"]
def unitIsoApp (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    A ≅ CategoryTheory.RelativeInertia.identitySection.obj F.toFunctor A.obj :=
  CategoryTheory.RelativeInertia.isoMk F.toFunctor (Iso.refl A.obj)
    (unitIsoApp.naturality F hX A)

/-- The explicit unit components are natural in relative-inertia morphisms. -/
theorem unitIso.naturality (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    {A B : (BasedCategory.relativeInertia F).obj} (phi : A ⟶ B) :
    (𝟭 (BasedCategory.relativeInertia F)).map phi ≫ (unitIsoApp F hX B).hom =
      (unitIsoApp F hX A).hom ≫
        (RelativeInertia.forget F ⋙ RelativeInertia.identitySection F).map phi := sorry

/-- Every explicit unit component lies over the identity of the base. -/
theorem unitIso.isHomLift (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    (BasedCategory.relativeInertia F).p.IsHomLift
      (𝟙 ((BasedCategory.relativeInertia F).p.obj A)) (unitIsoApp F hX A).hom := sorry

/-- The canonical unit comparing identity with forgetting followed by the neutral section. -/
@[stacks 04Z3 "relative-inertia unit isomorphism in setoid fibres"]
def unitIso (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p) :
    𝟙 (BasedCategory.relativeInertia F) ≅
      RelativeInertia.forget F ⋙ RelativeInertia.identitySection F :=
  BasedNatIso.ofComponents (unitIsoApp F hX)
    (unitIso.naturality F hX) (unitIso.isHomLift F hX)

/-- Identity components give a natural comparison from the neutral-section composite to identity. -/
theorem counitIso.naturality (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    (RelativeInertia.identitySection F ⋙ RelativeInertia.forget F).map f ≫
        (Iso.refl y).hom =
      (Iso.refl x).hom ≫ (𝟭 X).map f := sorry

/-- The identity component of the counit lies over the identity of the base. -/
theorem counitIso.isHomLift (F : X ⥤ᵇ Y) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x)) (Iso.refl x).hom := sorry

/-- The canonical counit comparing the neutral section followed by forgetting with identity. -/
@[stacks 04Z3 "relative-inertia counit isomorphism"]
def counitIso (F : X ⥤ᵇ Y) :
    RelativeInertia.identitySection F ⋙ RelativeInertia.forget F ≅ 𝟙 X :=
  BasedNatIso.ofComponents (fun x ↦ Iso.refl x)
    (counitIso.naturality F) (counitIso.isHomLift F)

/-- Relative inertia over a source with setoid fibres is canonically equivalent to the source. -/
@[stacks 04Z3 "relative-inertia equivalence in setoid fibres"]
def equivalenceOf (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p) :
    BasedCategory.relativeInertia F ≌ X :=
  Bicategory.Equivalence.mkOfAdjointifyUnit (unitIso F hX) (counitIso F)

/-- The forward morphism of the relative-inertia equivalence is forgetting. -/
@[simp] theorem equivalenceOf.hom (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p) :
    (equivalenceOf F hX).hom = RelativeInertia.forget F := sorry

/-- The inverse morphism of the relative-inertia equivalence is the neutral section. -/
@[simp] theorem equivalenceOf.inv (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p) :
    (equivalenceOf F hX).inv = RelativeInertia.identitySection F := sorry

/-- The canonical relative-inertia equivalence is independent of the proof of thinness. -/
theorem equivalenceOf.eq (F : X ⥤ᵇ Y) (hX hX' : Functor.IsFibered.InSetoids X.p) :
    equivalenceOf F hX = equivalenceOf F hX' := sorry

end BasedCategory.RelativeInertia.forget

namespace BasedCategory.Inertia.forget

variable {C : Type u} [Category.{v} C]

/-- Absolute inertia of a based category with setoid fibres is canonically equivalent to the category. -/
@[stacks 04Z3 "inertia equivalence in setoid fibres"]
def equivalenceOf (X : BasedCategory.{vS, max w vS} C)
    (hX : Functor.IsFibered.InSetoids X.p) : BasedCategory.inertia X ≌ X :=
  BasedCategory.RelativeInertia.forget.equivalenceOf X.toBase hX

/-- The forward morphism of the absolute-inertia equivalence is forgetting. -/
@[simp] theorem equivalenceOf.hom (X : BasedCategory.{vS, max w vS} C)
    (hX : Functor.IsFibered.InSetoids X.p) :
    (equivalenceOf X hX).hom = BasedCategory.Inertia.forget X := sorry

/-- The inverse morphism of the absolute-inertia equivalence is the neutral section. -/
@[simp] theorem equivalenceOf.inv (X : BasedCategory.{vS, max w vS} C)
    (hX : Functor.IsFibered.InSetoids X.p) :
    (equivalenceOf X hX).inv = BasedCategory.Inertia.identitySection X := sorry

/-- The canonical absolute-inertia equivalence is independent of the proof of thinness. -/
theorem equivalenceOf.eq (X : BasedCategory.{vS, max w vS} C)
    (hX hX' : Functor.IsFibered.InSetoids X.p) :
    equivalenceOf X hX = equivalenceOf X hX' := sorry

end BasedCategory.Inertia.forget
end CategoryTheory
