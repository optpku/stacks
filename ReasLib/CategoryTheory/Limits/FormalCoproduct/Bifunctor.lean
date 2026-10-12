/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import ReasLib.CategoryTheory.Functor.PointwiseBifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Bifunctors on formal-coproduct presheaves

For a curried bifunctor `T : A ⥤ B ⥤ D`, evaluation on a formal coproduct gives products in
`A` and `B`.  This file owns the canonical map from `T` applied to those two products to the
product of the pointwise `T`-values.  No monoidal unit or same-universe hypothesis is used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Opposite

noncomputable section

universe w uA vA uB vB uD vD v u

namespace CategoryTheory.Limits.FormalCoproduct.Bifunctor

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]
variable {B : Type uB} [Category.{vB} B] [HasProducts.{w} B]
variable {D : Type uD} [Category.{vD} D]

/-- Apply a coefficient bifunctor pointwise to two presheaves. -/
@[stacks 07MB "pointwise coefficient bifunctor on presheaves"]
abbrev pointwise (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B) : Cᵒᵖ ⥤ D :=
  Functor.PointwiseBifunctor.obj T F G

/-- Apply a coefficient bifunctor to two formal-coproduct evaluations. -/
@[stacks 07MB "coefficient bifunctor on formal-coproduct evaluations"]
abbrev evalOp (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B) :
    (FormalCoproduct.{w} C)ᵒᵖ ⥤ D :=
  (((Functor.whiskeringRight₂ (FormalCoproduct.{w} C)ᵒᵖ A B D).obj T).obj
    ((FormalCoproduct.evalOp.{w} C A).obj F)).obj
      ((FormalCoproduct.evalOp.{w} C B).obj G)

section TargetProducts

variable [HasProducts.{w} D]

/-- The explicit component from bifunctor-applied products to the product of pointwise values. -/
@[stacks 07MB "formal-coproduct bifunctor component"]
noncomputable def app (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    (X : (FormalCoproduct.{w} C)ᵒᵖ) :
    (evalOp T F G).obj X ⟶
      ((FormalCoproduct.evalOp.{w} C D).obj (pointwise T F G)).obj X :=
  Pi.lift (fun i ↦
    (T.map (Pi.π (fun j : X.unop.I ↦
      F.obj (op (X.unop.obj j))) i)).app
        (((FormalCoproduct.evalOp.{w} C B).obj G).obj X) ≫
      (T.obj (F.obj (op (X.unop.obj i)))).map
        (Pi.π (fun j : X.unop.I ↦
          G.obj (op (X.unop.obj j))) i))

/-- Naturality of the formal-coproduct bifunctor component. -/
@[reassoc, stacks 07MB "naturality of the formal-coproduct bifunctor component"]
theorem app_naturality (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    {X Y : (FormalCoproduct.{w} C)ᵒᵖ} (f : X ⟶ Y) :
    (evalOp T F G).map f ≫ app T F G Y =
      app T F G X ≫
        ((FormalCoproduct.evalOp.{w} C D).obj (pointwise T F G)).map f := sorry

/-- The formal-coproduct bifunctor comparison as a natural transformation. -/
@[stacks 07MB "formal-coproduct bifunctor comparison"]
noncomputable def hom (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B) :
    evalOp T F G ⟶ (FormalCoproduct.evalOp.{w} C D).obj (pointwise T F G) where
  app X := app T F G X
  naturality _ _ f := app_naturality T F G f

end TargetProducts

end CategoryTheory.Limits.FormalCoproduct.Bifunctor

end
