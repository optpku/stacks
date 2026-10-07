module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Basic
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# From strong transformations to indexed functors

This leaf converts a strong transformation between `Cat`-valued pseudofunctors on a locally
discrete opposite into the universe-polymorphic indexed-functor owner.
-/

@[expose] public section

universe uC vC uF vF

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}

/-- The indexed naturality isomorphism obtained from a strong transformation on
`LocallyDiscrete Cᵒᵖ`. -/
def toIndexedFunctorNaturality
    (eta : StrongTrans F G) {U V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor ⋙
        (eta.app (.mk (op V))).toFunctor ≅
      (eta.app (.mk (op U))).toFunctor ⋙
        (G.map ((𝟭 C).map f).op.toLoc).toFunctor :=
  Cat.Hom.toNatIso (eta.naturality f.op.toLoc)

/-- Identity coherence for the indexed naturality obtained from a strong transformation. -/
theorem toIndexedFunctorNaturality.identity
    (eta : StrongTrans F G) (U : C)
    (x : F.obj (LocallyDiscrete.mk (op U))) :
    (eta.app (.mk (op U))).toFunctor.map
          ((F.mapIdOp U).inv.toNatTrans.app x) ≫
        (toIndexedFunctorNaturality eta (𝟙 U)).hom.app x =
      (G.mapIdOp' ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app
          ((eta.app (.mk (op U))).toFunctor.obj x) := sorry

/-- Composition coherence for the indexed naturality obtained from a strong transformation. -/
theorem toIndexedFunctorNaturality.composition
    (eta : StrongTrans F G)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (LocallyDiscrete.mk (op U))) :
    (toIndexedFunctorNaturality eta (g ≫ f)).hom.app x ≫
        (G.mapCompOp' ((𝟭 C).map f) ((𝟭 C).map g)
          ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app
            ((eta.app (.mk (op U))).toFunctor.obj x) =
      (eta.app (.mk (op W))).toFunctor.map
          ((F.mapCompOp f g).hom.toNatTrans.app x) ≫
        (toIndexedFunctorNaturality eta g).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (G.map ((𝟭 C).map g).op.toLoc).toFunctor.map
          ((toIndexedFunctorNaturality eta f).hom.app x) := sorry

/-- Convert a strong transformation on a locally discrete opposite into the canonical indexed
functor over the identity of `C`. The component and naturality data are inherited directly from
the strong transformation; only the identity and composition coherence fields are Prop-valued. -/
def toIndexedFunctor (eta : StrongTrans F G) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C) F G where
  app U := (eta.app (.mk (op U))).toFunctor
  naturality f := toIndexedFunctorNaturality eta f
  naturality_id U x := toIndexedFunctorNaturality.identity eta U x
  naturality_comp f g x :=
    toIndexedFunctorNaturality.composition eta f g x

/-- The component of `toIndexedFunctor` is the corresponding strong-transformation component. -/
@[simp]
theorem toIndexedFunctor.app (eta : StrongTrans F G) (U : C) :
    eta.toIndexedFunctor.app U = (eta.app (.mk (op U))).toFunctor := sorry

/-- The naturality comparison of `toIndexedFunctor` is the corresponding strong-transformation
naturality comparison on the locally discrete arrow. -/
@[simp]
theorem toIndexedFunctor.naturality
    (eta : StrongTrans F G) {U V : C} (f : V ⟶ U) :
    eta.toIndexedFunctor.naturality f =
      toIndexedFunctorNaturality eta f := sorry

/-- Forward indexed naturality is forward strong naturality on each object. -/
@[simp]
theorem toIndexedFunctor.naturality.hom.app
    (eta : StrongTrans F G) {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (op U))) :
    (eta.toIndexedFunctor.naturality f).hom.app x =
      (eta.naturality f.op.toLoc).hom.toNatTrans.app x := sorry

/-- Inverse indexed naturality is inverse strong naturality on each object. -/
@[simp]
theorem toIndexedFunctor.naturality.inv.app
    (eta : StrongTrans F G) {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (op U))) :
    (eta.toIndexedFunctor.naturality f).inv.app x =
      (eta.naturality f.op.toLoc).inv.toNatTrans.app x := sorry

end Pseudofunctor.StrongTrans

end CategoryTheory
