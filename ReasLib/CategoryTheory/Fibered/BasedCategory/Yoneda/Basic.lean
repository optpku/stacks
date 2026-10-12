/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity-slice evaluation for based categories

This file owns evaluation at the identity slice object for the category of strictly based
functors `C/U ⥤ S`.  It does not assume that `S ⥤ C` is fibred and does not choose an inverse to
evaluation.  Cartesian comparison and groupoid-fibred equivalence APIs live in downstream leaves.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace BasedCategory.Yoneda

/-- The category of strictly based functors from the slice projection `C/U` to `p : S ⥤ C`. -/
abbrev hom (p : S ⥤ C) (U : C) :=
  BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p

/-- The identity slice object, packaged in the standard fiber of `Over.forget U` over `U`. -/
@[stacks 004B "identity slice fiber object"]
def Identity.fiberObj (U : C) : (Over.forget U).Fiber U :=
  ⟨Over.mk (𝟙 U), rfl⟩

/-- Evaluation of based slice functors at `𝟙 U`, valued in the standard fiber of `p`. -/
@[stacks 004B "identity-slice evaluation"]
noncomputable def evaluation (p : S ⥤ C) (U : C) : hom p U ⥤ p.Fiber U :=
  BasedCategory.fiberFunctor
      (BasedCategory.ofFunctor (Over.forget U)) (BasedCategory.ofFunctor p) U ⋙
    (CategoryTheory.evaluation _ _).obj (Identity.fiberObj U)

/-- After forgetting the fiber packaging, identity-slice evaluation sends a based functor to its
value at `Over.mk (𝟙 U)`. -/
@[simp]
theorem evaluation.obj (p : S ⥤ C) (U : C) (F : hom p U) :
    (Fiber.fiberInclusion : p.Fiber U ⥤ S).obj ((evaluation p U).obj F) =
      F.toFunctor.obj (Over.mk (𝟙 U)) := sorry

/-- After forgetting the fiber packaging, identity-slice evaluation sends a based natural
transformation to its component at `Over.mk (𝟙 U)`. -/
@[simp]
theorem evaluation.map (p : S ⥤ C) (U : C) {F G : hom p U} (η : F ⟶ G) :
    (Fiber.fiberInclusion : p.Fiber U ⥤ S).map ((evaluation p U).map η) =
      η.toNatTrans.app (Over.mk (𝟙 U)) := sorry

end BasedCategory.Yoneda

end CategoryTheory
