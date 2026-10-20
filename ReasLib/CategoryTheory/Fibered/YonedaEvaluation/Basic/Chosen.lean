/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Basic.Explicit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen-cleavage fixed-owner Yoneda equivalence

This leaf specializes the explicit fixed-owner Yoneda API to the cleavage stored by a bundled
fibred category and supplies direct computation and naturality entry points for downstream use.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Functor
open Functor.Fiber
open FiberedCategoryOver

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.YonedaSlice

variable (X : FiberedCategoryOver C)

namespace QuasiInverse

/-- The Yoneda section built from the cleavage selected directly from the fibredness witness
stored by `X`. -/
@[stacks 0GWI "selected-cleavage Yoneda section"]
noncomputable def functor (U : C) :
    X.p.Fiber U ⥤ (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :=
  sectionOfCleavage X X.chosenCleavage U

namespace functor

/-- The selected section object is the corresponding explicit-cleavage section object. -/
@[simp]
theorem obj (U : C) (x : X.p.Fiber U) :
    (QuasiInverse.functor X U).obj x =
      (sectionOfCleavage X X.chosenCleavage U).obj x := sorry

/-- The selected section map has the underlying vertical transformation of the corresponding
explicit-cleavage section map. -/
theorem map.hom {U : C} {x y : X.p.Fiber U} (f : x ⟶ y) :
    ((QuasiInverse.functor X U).map f).hom =
      ((sectionOfCleavage X X.chosenCleavage U).map f).hom := sorry

end functor

/-- A morphism from the slice into `X` is canonically isomorphic to the selected section of its
value at the identity slice object. -/
@[stacks 0GWI "selected-cleavage Yoneda unit"]
noncomputable def unitIso.app {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    F ≅ (functor X U).obj ((evaluation X U).obj F) :=
  sectionOfCleavage.unitIso.app X X.chosenCleavage F

/-- Evaluating the selected Yoneda section at the identity slice object recovers the original
fiber object. -/
@[stacks 0GWI "selected-cleavage Yoneda counit"]
noncomputable def counitIso.app {U : C} (x : X.p.Fiber U) :
    (evaluation X U).obj ((functor X U).obj x) ≅ x :=
  sectionOfCleavage.counitIso.app X X.chosenCleavage x

namespace unitIso

/-- Naturality of the forward selected-cleavage Yoneda unit. -/
@[reassoc]
theorem hom.naturality {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X} (eta : F ⟶ G) :
    eta ≫ (unitIso.app X G).hom =
      (unitIso.app X F).hom ≫ (functor X U).map ((evaluation X U).map eta) := sorry

/-- Naturality of the inverse selected-cleavage Yoneda unit. -/
@[reassoc]
theorem inv.naturality {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X} (eta : F ⟶ G) :
    (functor X U).map ((evaluation X U).map eta) ≫ (unitIso.app X G).inv =
      (unitIso.app X F).inv ≫ eta := sorry

end unitIso

namespace counitIso

/-- Naturality of the forward selected-cleavage Yoneda counit. -/
@[reassoc]
theorem hom.naturality {U : C} {x y : X.p.Fiber U} (f : x ⟶ y) :
    (evaluation X U).map ((functor X U).map f) ≫ (counitIso.app X y).hom =
      (counitIso.app X x).hom ≫ f := sorry

/-- Naturality of the inverse selected-cleavage Yoneda counit. -/
@[reassoc]
theorem inv.naturality {U : C} {x y : X.p.Fiber U} (f : x ⟶ y) :
    f ≫ (counitIso.app X y).inv =
      (counitIso.app X x).inv ≫ (evaluation X U).map ((functor X U).map f) := sorry

end counitIso

end QuasiInverse

/-- The selected-cleavage Yoneda unit components assembled into a natural isomorphism. -/
@[stacks 0GWI "selected-cleavage Yoneda unit natural isomorphism"]
noncomputable def QuasiInverse.unitIso (U : C) :
    𝟭 (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) ≅
      evaluation X U ⋙ QuasiInverse.functor X U :=
  sectionOfCleavage.unitIso X X.chosenCleavage U

/-- The selected-cleavage Yoneda counit components assembled into a natural isomorphism. -/
@[stacks 0GWI "selected-cleavage Yoneda counit natural isomorphism"]
noncomputable def QuasiInverse.counitIso (U : C) :
    QuasiInverse.functor X U ⋙ evaluation X U ≅ 𝟭 (X.p.Fiber U) :=
  sectionOfCleavage.counitIso X X.chosenCleavage U

/-- A forward component of the packaged selected unit is its named objectwise comparison. -/
@[simp]
theorem QuasiInverse.unitIso.hom.app (U : C)
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    (QuasiInverse.unitIso X U).hom.app F = (QuasiInverse.unitIso.app X F).hom := sorry

/-- An inverse component of the packaged selected unit is its named objectwise comparison. -/
@[simp]
theorem QuasiInverse.unitIso.inv.app (U : C)
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    (QuasiInverse.unitIso X U).inv.app F = (QuasiInverse.unitIso.app X F).inv := sorry

/-- A forward component of the packaged selected counit is its named objectwise comparison. -/
@[simp]
theorem QuasiInverse.counitIso.hom.app (U : C) (x : X.p.Fiber U) :
    (QuasiInverse.counitIso X U).hom.app x = (QuasiInverse.counitIso.app X x).hom := sorry

/-- An inverse component of the packaged selected counit is its named objectwise comparison. -/
@[simp]
theorem QuasiInverse.counitIso.inv.app (U : C) (x : X.p.Fiber U) :
    (QuasiInverse.counitIso X U).inv.app x = (QuasiInverse.counitIso.app X x).inv := sorry

/-- Explicit quasi-inverse data for fixed-owner Yoneda evaluation selected from `X`. -/
@[stacks 0GWI "selected-cleavage Yoneda quasi-inverse"]
noncomputable def quasiInverse (U : C) : Functor.QuasiInverse (evaluation X U) :=
  sectionOfCleavage.quasiInverse X X.chosenCleavage U

namespace quasiInverse

/-- The inverse stored by the selected quasi-inverse is the selected section. -/
@[simp]
theorem inverse (U : C) :
    (YonedaSlice.quasiInverse X U).inverse = QuasiInverse.functor X U := sorry

/-- The unit stored by the selected quasi-inverse is the selected unit. -/
@[simp]
theorem unitIso (U : C) :
    (YonedaSlice.quasiInverse X U).unitIso = QuasiInverse.unitIso X U := sorry

/-- The counit stored by the selected quasi-inverse is the selected counit. -/
@[simp]
theorem counitIso (U : C) :
    (YonedaSlice.quasiInverse X U).counitIso = QuasiInverse.counitIso X U := sorry

end quasiInverse

/-- The fixed-owner Yoneda equivalence with the selected-cleavage section as inverse. -/
@[stacks 0GWI "fibered Yoneda equivalence"]
noncomputable def equivalence (U : C) :
    (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) ≌ X.p.Fiber U :=
  sectionOfCleavage.equivalence X X.chosenCleavage U

/-- The forward functor retained by the selected equivalence is evaluation. -/
@[simp]
theorem equivalence.functor (U : C) :
    (equivalence X U).functor = evaluation X U := sorry

/-- The inverse retained by the selected equivalence is the selected section. -/
@[simp]
theorem equivalence.inverse (U : C) :
    (equivalence X U).inverse = QuasiInverse.functor X U := sorry

/-- The counit retained by the selected equivalence is the selected counit. -/
@[simp]
theorem equivalence.counitIso (U : C) :
    (equivalence X U).counitIso = QuasiInverse.counitIso X U := sorry

/-- Fixed-owner Yoneda evaluation is an equivalence, with inverse represented by the selected
cleavage section. -/
@[stacks 0GWI]
noncomputable instance evaluation.isEquivalence (U : C) :
    (evaluation X U).IsEquivalence := sorry

end FiberedCategoryOver.YonedaSlice

end CategoryTheory

/- Data audit: selected section and comparison data specialize the explicit owner at
`X.chosenCleavage`; deferred axioms occur only in computation, naturality, and coherence fields. -/
