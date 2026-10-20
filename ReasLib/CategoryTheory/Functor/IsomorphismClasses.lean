/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors out of isomorphism classes

This module contains the canonical map induced by a functor from object
isomorphism classes into a discrete target category.
-/

@[expose] public section

universe w uD vD uE vE uK vK

namespace CategoryTheory.Functor

variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- The map on object isomorphism classes induced by a functor. Unlike
`isomorphismClasses.map`, this function allows the source and target categories to have unrelated
object and morphism universes. -/
@[stacks 02Y9 "universe-polymorphic action on object isomorphism classes",
  stacks 0CKJ "universe-polymorphic action on object isomorphism classes"]
def isoClassesMap (G : D ⥤ E) :
    isomorphismClasses.obj (Cat.of D) →
      isomorphismClasses.obj (Cat.of E) :=
  Quotient.map G.obj fun _ _ ⟨e⟩ ↦ ⟨G.mapIso e⟩

/- Axiom audit: both the quotient function and its `mapIso` well-definedness witness are explicit;
the data owner does not use `sorryAx`. -/

namespace isoClassesMap

/-- The induced map sends the class represented by `x` to the class represented by `G.obj x`. -/
@[simp]
theorem mk (G : D ⥤ E) (x : D) :
    G.isoClassesMap (Quotient.mk'' x) = Quotient.mk'' (G.obj x) := sorry

/-- The map on isomorphism classes after lifting both sides into a common ambient universe. The
extra universe parameter lets several maps be lifted into one common universe before composing. -/
@[stacks 02Y9 "ambient-universe action on object isomorphism classes",
  stacks 0CKJ "ambient-universe action on object isomorphism classes"]
def ulift (G : D ⥤ E) :
    ULift.{max w uD uE} (isomorphismClasses.obj (Cat.of D)) →
      ULift.{max w uD uE} (isomorphismClasses.obj (Cat.of E)) :=
  fun x ↦ ULift.up (G.isoClassesMap x.down)

/-- The lifted map sends a lifted represented class to the lifted class of its image. -/
@[simp]
theorem ulift.mk (G : D ⥤ E) (x : D) :
    ulift.{w} G (ULift.up (Quotient.mk'' x)) =
      ULift.up (Quotient.mk'' (G.obj x)) := sorry

/-- The identity functor induces the identity function on object isomorphism classes. -/
@[simp]
theorem id (D : Type uD) [Category.{vD} D] :
    (CategoryTheory.Functor.id D).isoClassesMap = fun x ↦ x := sorry

/-- Passing to object isomorphism classes preserves composition. -/
@[simp]
theorem comp
    {K : Type uK} [Category.{vK} K] (F : D ⥤ E) (G : E ⥤ K) :
    (F ⋙ G).isoClassesMap = G.isoClassesMap ∘ F.isoClassesMap := sorry

/-- After a common ambient lift, the identity functor still induces the identity function. -/
@[simp]
theorem ulift.id (D : Type uD) [Category.{vD} D] :
    ulift.{w} (CategoryTheory.Functor.id D) = fun x ↦ x := sorry

/-- Lifted maps compose after all three object universes are included in the ambient lift. -/
@[simp]
theorem ulift.comp
    {K : Type uK} [Category.{vK} K] (F : D ⥤ E) (G : E ⥤ K) :
    ulift.{max w uE} (F ⋙ G) =
      ulift.{max w uD} G ∘ ulift.{max w uK} F := sorry

/-- In a fixed category universe, `isoClassesMap` agrees with the map of mathlib's
`isomorphismClasses` functor. -/
theorem eq_map
    {D' E' : Type uD} [Category.{vD} D'] [Category.{vD} E'] (G : D' ⥤ E') :
    TypeCat.ofHom G.isoClassesMap =
      isomorphismClasses.map G.toCatHom := sorry

end isoClassesMap

/-- The canonical map from source-object isomorphism classes to target objects, when the target
category is discrete. For a groupoid source this is the induced map on `π₀`. -/
@[stacks 02Y2 "isomorphism classes into a discrete category",
  stacks 04SI "isomorphism classes into a discrete category"]
def isoClassesToObj (G : D ⥤ E) [IsDiscrete E] :
    isomorphismClasses.obj (Cat.of D) → E :=
  Quotient.lift G.obj fun _ _ ⟨e⟩ ↦
    obj_ext_of_isDiscrete (G.mapIso e).hom

/-- The canonical `π₀` map sends the class represented by `x` to `G.obj x`. -/
@[simp]
theorem isoClassesToObj.mk (G : D ⥤ E) [IsDiscrete E] (x : D) :
    G.isoClassesToObj (Quotient.mk'' x) = G.obj x := sorry
/- Proof strategy: unfold `isoClassesToObj`; the computation rule for `Quotient.lift` evaluates it
on `Quotient.mk'' x` to `G.obj x`. -/

/-- Mapping isomorphism classes and then reading them in a discrete target is the same as reading
the composite functor directly. This is the mixed composition law between `isoClassesMap` and
`isoClassesToObj`. -/
@[simp]
theorem isoClassesToObj.comp
    {K : Type uK} [Category.{vK} K] [IsDiscrete K]
    (F : D ⥤ E) (G : E ⥤ K) :
    (F ⋙ G).isoClassesToObj = G.isoClassesToObj ∘ F.isoClassesMap := sorry

/-- The canonical map to a discrete target after placing both its source classes and target
objects in a common ambient universe. The extra universe parameter allows this map to compose
with other lifted maps without fixing a minimal universe. -/
@[stacks 02Y2 "ambient-universe discrete-target class map",
  stacks 04SI "ambient-universe discrete-target class map"]
def isoClassesToObj.ulift (G : D ⥤ E) [IsDiscrete E] :
    ULift.{max w uD uE} (isomorphismClasses.obj (Cat.of D)) →
      ULift.{max w uD uE} E :=
  fun x ↦ ULift.up (G.isoClassesToObj x.down)

/-- The lifted discrete-target map sends a lifted represented class to the lifted image of its
representative. -/
@[simp]
theorem isoClassesToObj.ulift.mk (G : D ⥤ E) [IsDiscrete E] (x : D) :
    isoClassesToObj.ulift.{w} G (ULift.up (Quotient.mk'' x)) =
      ULift.up (G.obj x) := sorry

/-- The mixed composition law remains valid after all three object universes are included in a
common ambient lift. -/
@[simp]
theorem isoClassesToObj.ulift.comp
    {K : Type uK} [Category.{vK} K] [IsDiscrete K]
    (F : D ⥤ E) (G : E ⥤ K) :
    isoClassesToObj.ulift.{max w uE} (F ⋙ G) =
      isoClassesToObj.ulift.{max w uD} G ∘
        isoClassesMap.ulift.{max w uK} F := sorry

namespace IsEquivalence

/-- An equivalence into a discrete category identifies source-object isomorphism classes with
target objects. The forward map is `isoClassesToObj`, and the inverse sends a target object to
the isomorphism class of its image under the named inverse functor. -/
@[stacks 0045 "isomorphism classes under an equivalence to a discrete category",
  stacks 04SI "isomorphism classes under an equivalence to a discrete category"]
noncomputable def isoClassesEquiv
    (G : D ⥤ E) [G.IsEquivalence] [IsDiscrete E] :
    isomorphismClasses.obj (Cat.of D) ≃ E where
  toFun := G.isoClassesToObj
  invFun := fun y => Quotient.mk'' (G.inv.obj y)
  left_inv := sorry
  right_inv := sorry
/- Axiom audit: `toFun` is the canonical quotient map and `invFun` uses the named mathlib
quasi-inverse. Only the two Prop-valued inverse laws remain deferred. -/

/-- The forward map of `Functor.IsEquivalence.isoClassesEquiv` sends a represented isomorphism
class to the image of its representative. -/
@[simp]
theorem isoClassesEquiv.apply
    (G : D ⥤ E) [G.IsEquivalence] [IsDiscrete E] (x : D) :
    IsEquivalence.isoClassesEquiv G (Quotient.mk'' x) = G.obj x := sorry
/- Proof strategy: apply `isoClassesToObj.mk` to `G`. -/

/-- The inverse map of `Functor.IsEquivalence.isoClassesEquiv` is represented by the image under
the named inverse functor. -/
@[simp]
theorem isoClassesEquiv.symm_apply
    (G : D ⥤ E) [G.IsEquivalence] [IsDiscrete E] (y : E) :
    (IsEquivalence.isoClassesEquiv G).symm y = Quotient.mk'' (G.inv.obj y) := sorry
/- Proof strategy: unfold the inverse function of the explicit equivalence. -/

end IsEquivalence

/-- The canonical map to a discrete target is bijective when the functor is an equivalence. This
is the `Function.Bijective` projection of `Functor.IsEquivalence.isoClassesEquiv`. -/
theorem isoClassesToObj.bijective_of_isEquivalence
    (G : D ⥤ E) [G.IsEquivalence] [IsDiscrete E] :
    Function.Bijective G.isoClassesToObj := sorry
/- Proof strategy: take the bijectivity of `Functor.IsEquivalence.isoClassesEquiv G`. -/

end CategoryTheory.Functor

namespace CategoryTheory.Equivalence

variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- A specified equivalence into a discrete category identifies source-object isomorphism classes
with target objects. Unlike `Functor.IsEquivalence.isoClassesEquiv`, its inverse is computed
directly from the supplied `e.inverse`. -/
@[stacks 0045 "isomorphism classes under a specified equivalence to a discrete category",
  stacks 04SI "isomorphism classes under a specified equivalence to a discrete category"]
def isoClassesEquiv
    (e : D ≌ E) [IsDiscrete E] :
    isomorphismClasses.obj (Cat.of D) ≃ E where
  toFun := e.functor.isoClassesToObj
  invFun := fun y => Quotient.mk'' (e.inverse.obj y)
  left_inv := sorry
  right_inv := sorry
/- Axiom audit: both functions use the explicit functor and inverse stored in `e`; only the
Prop-valued inverse laws are deferred. -/

/-- The forward map of `isoClassesEquiv` sends a represented class to the image of
its representative under the supplied equivalence. -/
@[simp]
theorem isoClassesEquiv.apply
    (e : D ≌ E) [IsDiscrete E] (x : D) :
    e.isoClassesEquiv (Quotient.mk'' x) = e.functor.obj x := sorry
/- Proof strategy: apply `isoClassesToObj.mk` to `e.functor`. -/

/-- The inverse map of `isoClassesEquiv` is represented by the image under the
supplied inverse functor. -/
@[simp]
theorem isoClassesEquiv.symm_apply
    (e : D ≌ E) [IsDiscrete E] (y : E) :
    (e.isoClassesEquiv).symm y = Quotient.mk'' (e.inverse.obj y) := sorry
/- Proof strategy: unfold the inverse function of the explicit equivalence. -/

end CategoryTheory.Equivalence
