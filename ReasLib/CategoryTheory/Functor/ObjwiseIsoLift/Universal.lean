module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.EqToHom
public import ReasLib.CategoryTheory.Functor.ObjwiseIsoLift.Basic

/-!
# Universal property of prescribed objectwise lifts

This file keeps the source-facing uniqueness statement for an objectwise prescribed lift. The
canonical functor and comparison data are owned by `ObjwiseIsoLift.Basic`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.objwiseIsoLift

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ B)

/-- Lemma 4.2.18 (1) (Stacks 05SG): the prescribed object assignment and isomorphisms determine a
unique extension functor. This source-facing formulation retains the transports required to
state literal equality with the prescribed object function. -/
@[stacks 05SG "unique functor extending the chosen object assignment"]
theorem existsUnique
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    ∃! j : B ⥤ A,
      ∃ hjObj : ∀ X : B, j.obj X = jObj X,
        ∃ alpha : 𝟭 B ≅ j ⋙ F,
          ∀ X : B,
            alpha.hom.app X =
              (i X).hom ≫
                eqToHom (congrArg (fun Z ↦ F.obj Z) (hjObj X).symm) := sorry

end CategoryTheory.Functor.objwiseIsoLift
