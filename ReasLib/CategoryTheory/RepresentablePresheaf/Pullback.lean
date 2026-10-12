/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullbacks of set-valued presheaves

Pullbacks of presheaves are computed objectwise.  The comparison below identifies an evaluated
presheaf pullback with the explicit type of pairs satisfying the pullback equation.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {F G H : Cᵒᵖ ⥤ Type w}

/-- Evaluation of a pullback of set-valued presheaves is canonically isomorphic to the explicit
type-level pullback. -/
@[stacks 0022 "objectwise explicit fibre product of presheaves"]
noncomputable def presheafPullbackObjIso
    (a : F ⟶ G) (b : H ⟶ G) (X : C) :
    (pullback a b).obj (Opposite.op X) ≅
      Types.PullbackObj (a.app (Opposite.op X)) (b.app (Opposite.op X)) :=
  pullbackObjIso a b (Opposite.op X) ≪≫
    Types.pullbackIsoPullback (a.app (Opposite.op X)) (b.app (Opposite.op X))

/-- The forward objectwise pullback comparison reads its first coordinate as the evaluated first
pullback projection. -/
@[simp]
theorem presheafPullbackObjIso.hom_fst
    (a : F ⟶ G) (b : H ⟶ G) (X : C)
    (p : (pullback a b).obj (Opposite.op X)) :
    ((presheafPullbackObjIso a b X).hom p :
        F.obj (Opposite.op X) × H.obj (Opposite.op X)).fst =
      (pullback.fst a b).app (Opposite.op X) p := sorry

/-- The forward objectwise pullback comparison reads its second coordinate as the evaluated
second pullback projection. -/
@[simp]
theorem presheafPullbackObjIso.hom_snd
    (a : F ⟶ G) (b : H ⟶ G) (X : C)
    (p : (pullback a b).obj (Opposite.op X)) :
    ((presheafPullbackObjIso a b X).hom p :
        F.obj (Opposite.op X) × H.obj (Opposite.op X)).snd =
      (pullback.snd a b).app (Opposite.op X) p := sorry

/-- The inverse objectwise pullback comparison has evaluated first projection equal to the
first coordinate of the explicit pullback pair. -/
@[simp]
theorem presheafPullbackObjIso.inv_fst
    (a : F ⟶ G) (b : H ⟶ G) (X : C)
    (p : Types.PullbackObj (a.app (Opposite.op X)) (b.app (Opposite.op X))) :
    (pullback.fst a b).app (Opposite.op X) ((presheafPullbackObjIso a b X).inv p) =
      p.1.1 := sorry

/-- The inverse objectwise pullback comparison has evaluated second projection equal to the
second coordinate of the explicit pullback pair. -/
@[simp]
theorem presheafPullbackObjIso.inv_snd
    (a : F ⟶ G) (b : H ⟶ G) (X : C)
    (p : Types.PullbackObj (a.app (Opposite.op X)) (b.app (Opposite.op X))) :
    (pullback.snd a b).app (Opposite.op X) ((presheafPullbackObjIso a b X).inv p) =
      p.1.2 := sorry

end CategoryTheory.Limits
