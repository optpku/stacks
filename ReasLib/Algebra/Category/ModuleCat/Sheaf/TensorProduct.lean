module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Sheafified tensor products of module sheaves -/

@[expose] public section

open CategoryTheory

noncomputable section

universe uR v uC vC

namespace ModuleCat.TensorProduct.Sheaf

variable {C : Type uC} [Category.{vC} C]
variable (J : GrothendieckTopology C) (R : Type uR) [CommRing R]
variable [HasSheafify J (ModuleCat.{v} R)]

/-- Tensor product of module sheaves, obtained by sheafifying the pointwise tensor product. -/
def functor : Sheaf J (ModuleCat.{v} R) ⥤
    Sheaf J (ModuleCat.{v} R) ⥤ Sheaf J (ModuleCat.{v} R) :=
  sheafToPresheaf J (ModuleCat.{v} R) ⋙
    ModuleCat.TensorProduct.Presheaf.functor ⋙
    (Functor.whiskeringLeft (Sheaf J (ModuleCat.{v} R))
      (Cᵒᵖ ⥤ ModuleCat.{v} R) (Cᵒᵖ ⥤ ModuleCat.{v} R)).obj
        (sheafToPresheaf J (ModuleCat.{v} R)) ⋙
    (Functor.whiskeringRight (Sheaf J (ModuleCat.{v} R))
      (Cᵒᵖ ⥤ ModuleCat.{v} R) (Sheaf J (ModuleCat.{v} R))).obj
        (presheafToSheaf J (ModuleCat.{v} R))

/-- The tensor product object of two sheaves of modules. -/
abbrev obj (F G : Sheaf J (ModuleCat.{v} R)) : Sheaf J (ModuleCat.{v} R) :=
  ((functor J R).obj F).obj G

/-- The tensor product of module sheaves is the sheafification of their pointwise tensor. -/
theorem obj_eq_sheafify (F G : Sheaf J (ModuleCat.{v} R)) :
    obj J R F G = (presheafToSheaf J (ModuleCat.{v} R)).obj
      (ModuleCat.TensorProduct.Presheaf.obj F.obj G.obj) := rfl

/-- Tensor product of module sheaves is additive in the first variable. -/
instance functorAdditive : (functor J R).Additive := sorry

/-- Tensor product of module sheaves is additive in the second variable. -/
instance functorObjAdditive (F : Sheaf J (ModuleCat.{v} R)) :
    ((functor J R).obj F).Additive := sorry

end ModuleCat.TensorProduct.Sheaf

end
