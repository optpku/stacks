module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Fiber
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing Naturality for Pointwise Categorical Pullback Lifts

This leaf constructs the fibrewise reindexing comparisons for the universal lift and proves the
identity and composition coherence required to assemble them into an indexed functor.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uE vE uF vF uG vG uH vH uK vK

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {u : C ⥤ D} {v : E ⥤ C}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

/-- Compatibility of the two indexed-naturality comparisons with the structural isomorphisms
of the source and target of pointwise-pullback lift naturality. -/
theorem Pullback.Lift.Naturality.isoApp.w
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (L.app (v.obj V)).map ((A.naturality f).hom.app x) ≫
        (((Pullback.Lift.Fiber.functor L R A B e U) ⋙
          ((Pullback.pseudofunctor L R).map
            (v.map f).op.toLoc).toFunctor).obj x).iso.hom =
      (((K.map f.op.toLoc).toFunctor ⋙
        Pullback.Lift.Fiber.functor L R A B e V).obj x).iso.hom ≫
        (R.app (v.obj V)).map ((B.naturality f).hom.app x) := sorry

/-- The objectwise naturality comparison for the indexed pointwise-pullback lift. -/
@[stacks 0040 "objectwise naturality of a pointwise categorical pseudo-pullback lift"]
noncomputable def Pullback.Lift.Naturality.isoApp
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((K.map f.op.toLoc).toFunctor ⋙
        Pullback.Lift.Fiber.functor L R A B e V).obj x ≅
      ((Pullback.Lift.Fiber.functor L R A B e U) ⋙
        ((Pullback.pseudofunctor L R).map
          (v.map f).op.toLoc).toFunctor).obj x :=
  CategoricalPullback.mkIso
    ((A.naturality f).app x)
    ((B.naturality f).app x)
    (Pullback.Lift.Naturality.isoApp.w L R A B e f x)

/-- The objectwise naturality comparisons for the indexed pointwise-pullback lift are natural
in the source fiber. -/
theorem Pullback.Lift.Naturality.isoApp.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    {x y : K.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y) :
    ((K.map f.op.toLoc).toFunctor ⋙
          Pullback.Lift.Fiber.functor L R A B e V).map φ ≫
        (Pullback.Lift.Naturality.isoApp L R A B e f y).hom =
      (Pullback.Lift.Naturality.isoApp L R A B e f x).hom ≫
        ((Pullback.Lift.Fiber.functor L R A B e U) ⋙
          ((Pullback.pseudofunctor L R).map
            (v.map f).op.toLoc).toFunctor).map φ := sorry

/-- Naturality of the indexed pointwise-pullback lift with respect to base reindexing. -/
@[stacks 0040 "naturality isomorphism of a pointwise categorical pseudo-pullback lift"]
noncomputable def Pullback.Lift.Naturality.iso
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U) :
    (K.map f.op.toLoc).toFunctor ⋙ Pullback.Lift.Fiber.functor L R A B e V ≅
      Pullback.Lift.Fiber.functor L R A B e U ⋙
        ((Pullback.pseudofunctor L R).map
          (v.map f).op.toLoc).toFunctor :=
  NatIso.ofComponents
    (Pullback.Lift.Naturality.isoApp L R A B e f)
    (fun φ ↦ Pullback.Lift.Naturality.isoApp.naturality L R A B e f φ)

/-- The left component of the forward naturality comparison for the indexed
pointwise-pullback lift is the forward naturality comparison of the left input. -/
@[simp]
theorem Pullback.Lift.Naturality.iso.hom.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.Naturality.iso L R A B e f).hom.app x).fst =
      (A.naturality f).hom.app x := sorry

/-- The right component of the forward naturality comparison for the indexed
pointwise-pullback lift is the forward naturality comparison of the right input. -/
@[simp]
theorem Pullback.Lift.Naturality.iso.hom.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.Naturality.iso L R A B e f).hom.app x).snd =
      (B.naturality f).hom.app x := sorry

/-- The left component of the inverse naturality comparison for the indexed
pointwise-pullback lift is the inverse naturality comparison of the left input. -/
@[simp]
theorem Pullback.Lift.Naturality.iso.inv.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.Naturality.iso L R A B e f).inv.app x).fst =
      (A.naturality f).inv.app x := sorry

/-- The right component of the inverse naturality comparison for the indexed
pointwise-pullback lift is the inverse naturality comparison of the right input. -/
@[simp]
theorem Pullback.Lift.Naturality.iso.inv.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.Naturality.iso L R A B e f).inv.app x).snd =
      (B.naturality f).inv.app x := sorry

/-- Identity coherence for the indexed pointwise-pullback lift. -/
theorem Pullback.Lift.ofCone.naturality_id
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    (U : E) (x : K.obj (LocallyDiscrete.mk (op U))) :
    (Pullback.Lift.Fiber.functor L R A B e U).map
          ((K.mapIdOp U).inv.toNatTrans.app x) ≫
        (Pullback.Lift.Naturality.iso L R A B e (𝟙 U)).hom.app x =
      ((Pullback.pseudofunctor L R).mapIdOp'
        (v.obj U) (v.map (𝟙 U))
        (v.map_id U)).inv.toNatTrans.app
          ((Pullback.Lift.Fiber.functor L R A B e U).obj x) := sorry

/-- Composition coherence for the indexed pointwise-pullback lift. -/
theorem Pullback.Lift.ofCone.naturality_comp
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V W : E} (f : V ⟶ U) (g : W ⟶ V)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (Pullback.Lift.Naturality.iso L R A B e (g ≫ f)).hom.app x ≫
        ((Pullback.pseudofunctor L R).mapCompOp'
          (v.map f) (v.map g) (v.map (g ≫ f))
          (v.map_comp g f).symm).hom.toNatTrans.app
            ((Pullback.Lift.Fiber.functor L R A B e U).obj x) =
      (Pullback.Lift.Fiber.functor L R A B e W).map
          ((K.mapCompOp f g).hom.toNatTrans.app x) ≫
        (Pullback.Lift.Naturality.iso L R A B e g).hom.app
          ((K.map f.op.toLoc).toFunctor.obj x) ≫
        ((Pullback.pseudofunctor L R).map
          (v.map g).op.toLoc).toFunctor.map
            ((Pullback.Lift.Naturality.iso L R A B e f).hom.app x) := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
