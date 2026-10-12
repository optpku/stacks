/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf

/-!
# Augmentations of fixed-target formal coproducts

This module gives the canonical map from the representable presheaf of a formal coproduct of
arrows into `X` to the representable presheaf of `X`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- A formal coproduct of arrows into `X` induces a canonical map from the associated coproduct
of representable presheaves to the representable presheaf of `X`. -/
noncomputable def augmentation {X : C} (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    toPresheaf.obj ((forgetOver X).obj K) ⟶ uliftYoneda.obj X :=
  Sigma.desc fun i : K.I ↦ uliftYoneda.{w}.map (K.obj i).hom

/-- The augmentation sends a canonical coproduct summand to composition with its structure map
to the fixed target. -/
@[simp] theorem augmentation_app_objMk {X : C} (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    (Y : Cᵒᵖ) (i : K.I) (g : Y.unop ⟶ ((forgetOver X).obj K).obj i) :
    (augmentation K).app Y (toPresheafObjMk ((forgetOver X).obj K) Y i g) =
      ULift.up (g ≫ (K.obj i).hom) := sorry

/-- The canonical augmentation is natural in morphisms of formal coproducts over the fixed
target. -/
@[reassoc] theorem augmentation_naturality {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)} (φ : K ⟶ L) :
    toPresheaf.map ((forgetOver X).map φ) ≫ augmentation L = augmentation K := sorry

end FormalCoproduct
end Limits
end CategoryTheory
