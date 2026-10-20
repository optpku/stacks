/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Section.Construction

/-!
# Naturality of the explicit-cleavage based Yoneda section

This file assembles the objectwise comparisons into natural isomorphisms and exposes both
orientations of their naturality and component computations.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {p : S ⥤ C}

namespace BasedCategory.Yoneda.sectionOfCleavage

namespace unitIso

/-- Naturality of the forward explicit-cleavage based Yoneda unit. -/
@[reassoc]
theorem hom.naturality [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) {U : C} {F G : BasedCategory.Yoneda.hom p U} (η : F ⟶ G) :
    η ≫ (unitIso.app χ G).hom =
      (unitIso.app χ F).hom ≫
        (sectionOfCleavage χ U).map ((BasedCategory.Yoneda.evaluation p U).map η) := sorry

/-- Naturality of the inverse explicit-cleavage based Yoneda unit. -/
@[reassoc]
theorem inv.naturality [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) {U : C} {F G : BasedCategory.Yoneda.hom p U} (η : F ⟶ G) :
    (sectionOfCleavage χ U).map ((BasedCategory.Yoneda.evaluation p U).map η) ≫
        (unitIso.app χ G).inv =
      (unitIso.app χ F).inv ≫ η := sorry

end unitIso

namespace counitIso

/-- Naturality of the forward explicit-cleavage based Yoneda counit. -/
@[reassoc]
theorem hom.naturality
    (χ : p.Cleavage) {U : C} {x y : p.Fiber U} (φ : x ⟶ y) :
    (BasedCategory.Yoneda.evaluation p U).map ((sectionOfCleavage χ U).map φ) ≫
        (counitIso.app χ y).hom =
      (counitIso.app χ x).hom ≫ φ := sorry

/-- Naturality of the inverse explicit-cleavage based Yoneda counit. -/
@[reassoc]
theorem inv.naturality
    (χ : p.Cleavage) {U : C} {x y : p.Fiber U} (φ : x ⟶ y) :
    φ ≫ (counitIso.app χ y).inv =
      (counitIso.app χ x).inv ≫
        (BasedCategory.Yoneda.evaluation p U).map ((sectionOfCleavage χ U).map φ) := sorry

end counitIso

/-- The objectwise explicit-cleavage Yoneda units assembled into a natural isomorphism. -/
@[stacks 004B "explicit-cleavage based Yoneda unit natural isomorphism"]
noncomputable def unitIso [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    𝟭 (BasedCategory.Yoneda.hom p U) ≅
      BasedCategory.Yoneda.evaluation p U ⋙ sectionOfCleavage χ U :=
  NatIso.ofComponents (unitIso.app χ)
    (fun η ↦ unitIso.hom.naturality χ η)

/-- The objectwise explicit-cleavage Yoneda counits assembled into a natural isomorphism. -/
@[stacks 004B "explicit-cleavage based Yoneda counit natural isomorphism"]
noncomputable def counitIso (χ : p.Cleavage) (U : C) :
    sectionOfCleavage χ U ⋙ BasedCategory.Yoneda.evaluation p U ≅ 𝟭 (p.Fiber U) :=
  NatIso.ofComponents (counitIso.app χ)
    (fun φ ↦ counitIso.hom.naturality χ φ)

/-- A forward component of the packaged based Yoneda unit is its explicit comparison. -/
@[simp]
theorem unitIso.hom.app [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) (F : BasedCategory.Yoneda.hom p U) :
    (unitIso χ U).hom.app F = (unitIso.app χ F).hom := sorry

/-- An inverse component of the packaged based Yoneda unit is its explicit comparison. -/
@[simp]
theorem unitIso.inv.app [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) (F : BasedCategory.Yoneda.hom p U) :
    (unitIso χ U).inv.app F = (unitIso.app χ F).inv := sorry

/-- A forward component of the packaged based Yoneda counit is its explicit comparison. -/
@[simp]
theorem counitIso.hom.app (χ : p.Cleavage) (U : C) (x : p.Fiber U) :
    (counitIso χ U).hom.app x = (counitIso.app χ x).hom := sorry

/-- An inverse component of the packaged based Yoneda counit is its explicit comparison. -/
@[simp]
theorem counitIso.inv.app (χ : p.Cleavage) (U : C) (x : p.Fiber U) :
    (counitIso χ U).inv.app x = (counitIso.app χ x).inv := sorry

end BasedCategory.Yoneda.sectionOfCleavage

end CategoryTheory
