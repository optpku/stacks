module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Pointwise tensor maps for formal coproduct presheaves

The extension `FormalCoproduct.evalOp` is defined by products.  This leaf records the canonical
map from the tensor of two such products to the product of the corresponding tensor factors.  It
is the coefficient-independent row map used by Cech Alexander--Whitney constructions; it does not
claim a tensor-preservation isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [HasProducts.{w} A]

/-- 20.25.3.2 (07MB): the indexed tensor map on one formal-coproduct component. -/
@[stacks 07MB "formal-coproduct tensor component"]
noncomputable def evalOpTensorApp (F G : Cᵒᵖ ⥤ A) (X : (FormalCoproduct.{w} C)ᵒᵖ) :
    (((evalOp.{w} C A).obj F) ⊗ ((evalOp.{w} C A).obj G)).obj X ⟶
      ((evalOp.{w} C A).obj (F ⊗ G)).obj X :=
  Pi.lift (fun i ↦
    Pi.π (fun j : X.unop.I ↦ F.obj (op (X.unop.obj j))) i ⊗ₘ
      Pi.π (fun j : X.unop.I ↦ G.obj (op (X.unop.obj j))) i)

/-- The pointwise tensor component is natural in the formal-coproduct argument. -/
@[stacks 07MB "formal-coproduct tensor naturality"]
theorem evalOpTensorApp_naturality (F G : Cᵒᵖ ⥤ A) {X Y : (FormalCoproduct.{w} C)ᵒᵖ}
    (f : X ⟶ Y) :
    (((evalOp.{w} C A).obj F) ⊗ ((evalOp.{w} C A).obj G)).map f ≫
        evalOpTensorApp F G Y =
      evalOpTensorApp F G X ≫ ((evalOp.{w} C A).obj (F ⊗ G)).map f := sorry

/-- 20.25.3.2 (07MB): the natural transformation of formal-coproduct tensor components. -/
@[stacks 07MB "formal-coproduct tensor map"]
noncomputable def evalOpTensorHom (F G : Cᵒᵖ ⥤ A) :
    ((evalOp.{w} C A).obj F) ⊗ ((evalOp.{w} C A).obj G) ⟶
      (evalOp.{w} C A).obj (F ⊗ G) where
  app X := evalOpTensorApp F G X
  naturality _ _ f := evalOpTensorApp_naturality F G f

/-- The formal-coproduct tensor map is natural in both coefficient presheaves. -/
@[reassoc, stacks 07MB "coefficient naturality of the formal-coproduct tensor map"]
theorem evalOpTensorHom_naturality
    {F F' G G' : Cᵒᵖ ⥤ A} (f : F ⟶ F') (g : G ⟶ G') :
    (((evalOp.{w} C A).map f) ⊗ₘ ((evalOp.{w} C A).map g)) ≫
        evalOpTensorHom F' G' =
      evalOpTensorHom F G ≫ (evalOp.{w} C A).map (f ⊗ₘ g) := sorry

end CategoryTheory.Limits.FormalCoproduct

end
