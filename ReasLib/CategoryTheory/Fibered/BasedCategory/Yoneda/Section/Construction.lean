/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection.Comparison
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Identity
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit-cleavage based Yoneda section

This file owns the section functor selected by a cleavage and the objectwise unit and counit
comparisons. Naturality and equivalence packaging live in downstream focused leaves.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {p : S ⥤ C}

namespace BasedCategory.Yoneda

/-- The inverse-direction Yoneda section determined by an explicit cleavage. -/
@[stacks 004B "explicit-cleavage based Yoneda section"]
noncomputable def sectionOfCleavage (χ : p.Cleavage) (U : C) :
    p.Fiber U ⥤ hom p U :=
  Functor.Cleavage.SliceSection.functor (BasedCategory.ofFunctor p) χ U ⋙
    CartesianBasedFunctor.forget (Over.forget U) p

namespace sectionOfCleavage

/-- The explicit-cleavage based Yoneda section sends a fiber object to its canonical based slice
section. -/
@[simp]
theorem obj (χ : p.Cleavage) (U : C) (x : p.Fiber U) :
    (sectionOfCleavage χ U).obj x =
      Functor.Cleavage.SliceSection.based (BasedCategory.ofFunctor p) χ U x := sorry

/-- The explicit-cleavage based Yoneda section sends a fiber morphism to the canonical vertical
transformation between its slice sections. -/
@[simp]
theorem map (χ : p.Cleavage) {U : C} {x y : p.Fiber U} (f : x ⟶ y) :
    (sectionOfCleavage χ U).map f =
      Functor.Cleavage.SliceSection.natTrans (BasedCategory.ofFunctor p) χ f := sorry

/-- A based functor from `C/U` is canonically isomorphic to the cleavage section of its value at
the identity slice object. -/
@[stacks 004B "explicit-cleavage based Yoneda unit"]
noncomputable def unitIso.app [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) {U : C} (F : hom p U) :
    F ≅ (sectionOfCleavage χ U).obj ((evaluation p U).obj F) :=
  Functor.Cleavage.SliceSection.Comparison.basedIso
    (BasedCategory.ofFunctor p) χ
      (CartesianBasedFunctor.ofTargetInGroupoids F)

/-- Evaluating an explicit cleavage section at the identity slice object recovers the original
fiber object. -/
@[stacks 004B "explicit-cleavage based Yoneda counit"]
noncomputable def counitIso.app (χ : p.Cleavage) {U : C} (x : p.Fiber U) :
    (evaluation p U).obj ((sectionOfCleavage χ U).obj x) ≅ x :=
  (Functor.Cleavage.Reindex.idIsoApp χ U x).symm

end sectionOfCleavage

end BasedCategory.Yoneda

end CategoryTheory
