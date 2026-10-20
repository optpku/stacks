/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Tensor products of module presheaves

This leaf keeps the tensor product heterogeneous: the two module presheaves may have different
carrier universes, and the result lives in their maximum universe.  It deliberately uses the
universe-polymorphic `ModuleCat.TensorProduct` bifunctor rather than the monoidal structure on
`ModuleCat`, whose unit imposes a same-universe restriction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uR vF vG uC vC

namespace ModuleCat.TensorProduct.Presheaf

variable {R : Type uR} [CommRing R]
variable {C : Type uC} [Category.{vC} C]

/-- The curried functor of heterogeneous tensor products of module presheaves. -/
@[stacks 07MB "curried heterogeneous tensor functor on module presheaves"]
abbrev functor :
    (Cᵒᵖ ⥤ ModuleCat.{vF} R) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{vG} R) ⥤
        (Cᵒᵖ ⥤ ModuleCat.{max vF vG} R) :=
  (Functor.whiskeringRight₂ Cᵒᵖ (ModuleCat.{vF} R) (ModuleCat.{vG} R)
    (ModuleCat.{max vF vG} R)).obj
      (ModuleCat.TensorProduct.functor.{uR, vF, vG} R)

/-- The objectwise tensor product of two module-valued presheaves. -/
@[stacks 07MB "objectwise heterogeneous tensor product of module presheaves"]
abbrev obj
    (F : Cᵒᵖ ⥤ ModuleCat.{vF} R) (G : Cᵒᵖ ⥤ ModuleCat.{vG} R) :
    Cᵒᵖ ⥤ ModuleCat.{max vF vG} R :=
  ((functor (R := R)).obj F).obj G

/-- The objectwise tensor map induced by two morphisms of module presheaves. -/
@[stacks 07MB "morphism of heterogeneous tensor presheaves"]
def hom
    {F F' : Cᵒᵖ ⥤ ModuleCat.{vF} R} {G G' : Cᵒᵖ ⥤ ModuleCat.{vG} R}
    (f : F ⟶ F') (g : G ⟶ G') : obj F G ⟶ obj F' G' :=
  ((functor (R := R)).map f).app G ≫ ((functor (R := R)).obj F').map g

/-- Evaluation of `obj` is the module tensor product at the same presheaf object. -/
@[simp, stacks 07MB "objectwise tensor presheaf evaluation"]
theorem obj_obj
    (F : Cᵒᵖ ⥤ ModuleCat.{vF} R) (G : Cᵒᵖ ⥤ ModuleCat.{vG} R) (U : Cᵒᵖ) :
    (obj F G).obj U = ModuleCat.TensorProduct.obj R (F.obj U) (G.obj U) := sorry

/-- Evaluation of `hom` is the tensor map of the evaluated morphisms. -/
@[simp, stacks 07MB "objectwise tensor presheaf morphism evaluation"]
theorem hom_app
    {F F' : Cᵒᵖ ⥤ ModuleCat.{vF} R} {G G' : Cᵒᵖ ⥤ ModuleCat.{vG} R}
    (f : F ⟶ F') (g : G ⟶ G') (U : Cᵒᵖ) :
    (hom f g).app U = ModuleCat.TensorProduct.map R (f.app U) (g.app U) := sorry

end ModuleCat.TensorProduct.Presheaf

end
