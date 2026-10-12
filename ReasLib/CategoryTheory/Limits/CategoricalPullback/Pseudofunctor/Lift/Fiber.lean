/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibrewise Pointwise Categorical Pullback Lifts

This leaf constructs the commutative square and functor in each fibre underlying a universal
indexed lift, together with projection computation rules.
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

/-- The ordinary categorical commutative square in a fiber underlying a pointwise-pullback
lift. -/
@[stacks 0040 "fiberwise cone underlying a pointwise categorical pseudo-pullback lift"]
noncomputable def Pullback.Lift.Fiber.cone
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    CatCommSqOver (L.app (v.obj U)) (R.app (v.obj U))
      (K.obj (LocallyDiscrete.mk (op U))) where
  fst := A.app U
  snd := B.app U
  iso := IndexedFunctor.isoApp e U

/-- The first functor of the fiberwise commutative square underlying a pointwise-pullback lift
is the first input component. -/
@[simp]
theorem Pullback.Lift.Fiber.cone.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    (Pullback.Lift.Fiber.cone L R A B e U).fst = A.app U := sorry

/-- The second functor of the fiberwise commutative square underlying a pointwise-pullback lift
is the second input component. -/
@[simp]
theorem Pullback.Lift.Fiber.cone.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    (Pullback.Lift.Fiber.cone L R A B e U).snd = B.app U := sorry

/-- The structural isomorphism of the fiberwise commutative square underlying a
pointwise-pullback lift is the corresponding component of the indexed compatibility
isomorphism. -/
@[simp]
theorem Pullback.Lift.Fiber.cone.iso
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    (Pullback.Lift.Fiber.cone L R A B e U).iso =
      IndexedFunctor.isoApp e U := sorry

/-- The component functor into a pointwise categorical pullback induced by two component
functors and an indexed compatibility isomorphism. -/
@[stacks 0040 "fiber functor of a pointwise categorical pseudo-pullback lift"]
noncomputable def Pullback.Lift.Fiber.functor
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    K.obj (LocallyDiscrete.mk (op U)) ⥤
      (L.app (v.obj U)) ⊡ (R.app (v.obj U)) :=
  (CatCommSqOver.toFunctorToCategoricalPullback
    (L.app (v.obj U)) (R.app (v.obj U)) _).obj
    (Pullback.Lift.Fiber.cone L R A B e U)

/-- The first projection of the component pointwise-pullback lift is the given left component
functor. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.compFst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    Pullback.Lift.Fiber.functor L R A B e U ⋙
        π₁ (L.app (v.obj U)) (R.app (v.obj U)) =
      A.app U := sorry

/-- The second projection of the component pointwise-pullback lift is the given right component
functor. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.compSnd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    Pullback.Lift.Fiber.functor L R A B e U ⋙
        π₂ (L.app (v.obj U)) (R.app (v.obj U)) =
      B.app U := sorry

/-- The left object component of the component pointwise-pullback lift. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.obj.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (Pullback.Lift.Fiber.functor L R A B e U |>.obj x).fst =
      (A.app U).obj x := sorry

/-- The right object component of the component pointwise-pullback lift. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.obj.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (Pullback.Lift.Fiber.functor L R A B e U |>.obj x).snd =
      (B.app U).obj x := sorry

/-- The structural isomorphism of an object under the component pointwise-pullback lift is the
corresponding component of the indexed compatibility isomorphism. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.obj.iso
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (Pullback.Lift.Fiber.functor L R A B e U |>.obj x).iso =
      (IndexedFunctor.isoApp e U).app x := sorry

/-- The left morphism component of the component pointwise-pullback lift. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.map.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    {x y : K.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y) :
    (Pullback.Lift.Fiber.functor L R A B e U |>.map φ).fst =
      (A.app U).map φ := sorry

/-- The right morphism component of the component pointwise-pullback lift. -/
@[simp]
theorem Pullback.Lift.Fiber.functor.map.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E)
    {x y : K.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y) :
    (Pullback.Lift.Fiber.functor L R A B e U |>.map φ).snd =
      (B.app U).map φ := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
