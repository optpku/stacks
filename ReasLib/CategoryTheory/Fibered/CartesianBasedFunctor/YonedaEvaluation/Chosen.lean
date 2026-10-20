/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Explicit

/-!
# Chosen cartesian Yoneda equivalence

This leaf specializes the explicit-cleavage cartesian Yoneda API to the cleavage selected by a
fibredness instance.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CartesianBasedFunctor.Yoneda

namespace Chosen

/-- The cartesian Yoneda section built from the cleavage selected by a fibredness instance. -/
@[stacks 0GWI "chosen-cleavage cartesian Yoneda section"]
noncomputable def functor (p : S ⥤ C) [p.IsFibered] (U : C) :
    p.Fiber U ⥤ hom p U :=
  sectionOfCleavage p (Functor.Cleavage.ofIsFibered p) U

namespace functor

/-- The chosen cartesian Yoneda section sends a fiber object to its selected cartesian slice
section. -/
@[simp, stacks 0GWI "chosen cartesian Yoneda object readout"]
theorem obj (p : S ⥤ C) [p.IsFibered] (U : C) (x : p.Fiber U) :
    (Chosen.functor p U).obj x =
      Functor.Cleavage.SliceSection.cartesian (BasedCategory.ofFunctor p)
        (Functor.Cleavage.ofIsFibered p) U x := sorry

/-- The chosen cartesian Yoneda section sends a fiber morphism to the selected vertical
transformation between its slice sections. -/
@[stacks 0GWI "chosen cartesian Yoneda morphism readout"]
theorem map.hom (p : S ⥤ C) [p.IsFibered] {U : C}
    {x y : p.Fiber U} (f : x ⟶ y) :
    ((Chosen.functor p U).map f).hom =
      Functor.Cleavage.SliceSection.natTrans (BasedCategory.ofFunctor p)
        (Functor.Cleavage.ofIsFibered p) f := sorry

end functor

/-- The explicit quasi-inverse data selected canonically from a fibredness instance. -/
@[stacks 0GWI "chosen-cleavage cartesian Yoneda quasi-inverse"]
noncomputable def quasiInverse (p : S ⥤ C) [p.IsFibered] (U : C) :
    Functor.QuasiInverse (evaluation p U) :=
  CartesianBasedFunctor.Yoneda.quasiInverse p (Functor.Cleavage.ofIsFibered p) U

/-- The cartesian Yoneda equivalence selected canonically from a fibredness instance. -/
@[stacks 0GWI "chosen-cleavage cartesian Yoneda equivalence"]
noncomputable def equivalence (p : S ⥤ C) [p.IsFibered] (U : C) :
    hom p U ≌ p.Fiber U :=
  CartesianBasedFunctor.Yoneda.equivalence p (Functor.Cleavage.ofIsFibered p) U

/-- The inverse functor stored by the chosen cartesian Yoneda quasi-inverse is the chosen
section. -/
@[simp, stacks 0GWI "chosen cartesian Yoneda inverse readout"]
theorem quasiInverse.inverse (p : S ⥤ C) [p.IsFibered] (U : C) :
    (quasiInverse p U).inverse = CartesianBasedFunctor.Yoneda.Chosen.functor p U := sorry

/-- The unit stored by the chosen cartesian Yoneda quasi-inverse is the unit associated to the
selected cleavage. -/
@[simp]
theorem quasiInverse.unitIso (p : S ⥤ C) [p.IsFibered] (U : C) :
    (quasiInverse p U).unitIso =
      CartesianBasedFunctor.Yoneda.unitIso p (Functor.Cleavage.ofIsFibered p) U := sorry

/-- The counit stored by the chosen cartesian Yoneda quasi-inverse is the counit associated to the
selected cleavage. -/
@[simp]
theorem quasiInverse.counitIso (p : S ⥤ C) [p.IsFibered] (U : C) :
    (quasiInverse p U).counitIso =
      CartesianBasedFunctor.Yoneda.counitIso p (Functor.Cleavage.ofIsFibered p) U := sorry

/-- The forward functor of the chosen cartesian Yoneda equivalence is evaluation. -/
@[simp]
theorem equivalence.functor (p : S ⥤ C) [p.IsFibered] (U : C) :
    (equivalence p U).functor = evaluation p U := sorry

/-- The inverse functor of the chosen cartesian Yoneda equivalence is the chosen section. -/
@[simp, stacks 0GWI "chosen cartesian Yoneda equivalence readout"]
theorem equivalence.inverse (p : S ⥤ C) [p.IsFibered] (U : C) :
    (equivalence p U).inverse = CartesianBasedFunctor.Yoneda.Chosen.functor p U := sorry

/-- The counit retained by the chosen cartesian Yoneda equivalence is the counit associated to the
selected cleavage. -/
@[simp]
theorem equivalence.counitIso (p : S ⥤ C) [p.IsFibered] (U : C) :
    (equivalence p U).counitIso =
      CartesianBasedFunctor.Yoneda.counitIso p (Functor.Cleavage.ofIsFibered p) U := sorry

end Chosen

/-- Fibered cartesian Yoneda evaluation is an equivalence, with the canonical representative
provided by `Chosen.quasiInverse`. -/
@[stacks 0GWI "universe-polymorphic cartesian Yoneda equivalence"]
noncomputable instance evaluation.isEquivalence (p : S ⥤ C) [p.IsFibered] (U : C) :
    (evaluation p U).IsEquivalence := sorry

end CartesianBasedFunctor.Yoneda

end CategoryTheory
