/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Verticality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia diagonal-comparison owner

This leaf owns the object-level and component-level data used to construct the canonical
comparison from relative inertia to the self-pseudo-pullback of the relative diagonal.  The
functorial assembly is kept in `Construction.Naturality`, while public projection equations are
kept in `Construction.Computations`.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC uS vS uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {S' : Type uS'} [Category.{vS'} S']
variable (F : S ⥤ S')
variable (p : S ⥤ C)
variable {p}
variable (p' : S' ⥤ C)

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace RelativeInertia.Implementation

/-- The inverse of a relative-inertia automorphism also maps to the identity. -/
private theorem map_inv_eq_id (X : RelativeInertia F) :
    F.map X.aut.inv = 𝟙 (F.obj X.obj) := by
  exact congrArg (fun e : Aut (F.obj X.obj) ↦ e.inv) X.mapAut_eq_one

/-- The identity component of the comparison lies over the base identity. -/
private theorem Comparison.hom_snd_isHomLift (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    p.IsHomLift (𝟙 (p.obj X.obj)) (𝟙 X.obj) := by
  infer_instance

/-- The forward comparison components satisfy the pseudo-pullback square. -/
private theorem Comparison.hom_comm (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    CommSq (F.map X.aut.hom)
      (PseudoPullback.comparison
        ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj))
      (PseudoPullback.comparison
        ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj))
      (F.map (𝟙 X.obj)) := by
  change CommSq (F.map X.aut.hom) (𝟙 _) (𝟙 _) (F.map (𝟙 X.obj))
  constructor
  have h : F.map X.aut.hom = 𝟙 (F.obj X.obj) :=
    congrArg (fun e : Aut (F.obj X.obj) ↦ e.hom) X.mapAut_eq_one
  simpa only [Category.comp_id, Category.id_comp, F.map_id] using h

/-- Forward component of the comparison from relative inertia to the diagonal self-pullback. -/
private def Comparison.hom (comm : F ⋙ p' = p) (X : RelativeInertia F) :
    (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj ⟶
      (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj :=
  PseudoPullback.Hom.mk (𝟙 (p.obj X.obj)) X.aut.hom
    (RelativeInertia.aut.hom.isHomLift comm X)
    (𝟙 X.obj) (Comparison.hom_snd_isHomLift F p' comm X)
    (Comparison.hom_comm F p' comm X)

/-- The forward comparison component is vertical in the diagonal pullback. -/
private theorem Comparison.hom_isHomLift (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    ((PseudoPullback (BasedFunctor.ofFunctor F comm)
      (BasedFunctor.ofFunctor F comm)).p).IsHomLift (𝟙 (p.obj X.obj))
      (Comparison.hom F p' comm X) := by
  exact Functor.IsHomLift.map (Comparison.hom F p' comm X)

/-- The inverse comparison components satisfy the pseudo-pullback square. -/
private theorem Comparison.inv_comm (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    CommSq (F.map X.aut.inv)
      (PseudoPullback.comparison
        ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj))
      (PseudoPullback.comparison
        ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj))
      (F.map (𝟙 X.obj)) := by
  change CommSq (F.map X.aut.inv) (𝟙 _) (𝟙 _) (F.map (𝟙 X.obj))
  constructor
  simpa only [Category.comp_id, Category.id_comp, F.map_id] using map_inv_eq_id F X

/-- Inverse component of the comparison from relative inertia to the diagonal self-pullback. -/
private def Comparison.inv (comm : F ⋙ p' = p) (X : RelativeInertia F) :
    (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj ⟶
      (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).obj X.obj :=
  PseudoPullback.Hom.mk (𝟙 (p.obj X.obj)) X.aut.inv
    (RelativeInertia.aut.inv.isHomLift comm X)
    (𝟙 X.obj) (Comparison.hom_snd_isHomLift F p' comm X)
    (Comparison.inv_comm F p' comm X)

/-- The inverse comparison component is vertical in the diagonal pullback. -/
private theorem Comparison.inv_isHomLift (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    ((PseudoPullback (BasedFunctor.ofFunctor F comm)
      (BasedFunctor.ofFunctor F comm)).p).IsHomLift (𝟙 (p.obj X.obj))
      (Comparison.inv F p' comm X) := by
  exact Functor.IsHomLift.map (Comparison.inv F p' comm X)

/-- A relative-inertia object lies in the fiber over its own base image. -/
private theorem Comparison.fiberObject_eq (X : RelativeInertia F) :
    p.obj X.obj = p.obj X.obj := by
  rfl

/-- Forward comparison morphism in the fiber of the relative diagonal. -/
private def Comparison.fiberHom (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).fiberFunctor
        (p.obj X.obj)).obj (Functor.Fiber.mk (Comparison.fiberObject_eq F X)) ⟶
      ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).fiberFunctor
        (p.obj X.obj)).obj (Functor.Fiber.mk (Comparison.fiberObject_eq F X)) :=
  ⟨Comparison.hom F p' comm X,
    Comparison.hom_isHomLift F p' comm X⟩

/-- Inverse comparison morphism in the fiber of the relative diagonal. -/
private def Comparison.fiberInv (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).fiberFunctor
        (p.obj X.obj)).obj (Functor.Fiber.mk (Comparison.fiberObject_eq F X)) ⟶
      ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).fiberFunctor
        (p.obj X.obj)).obj (Functor.Fiber.mk (Comparison.fiberObject_eq F X)) :=
  ⟨Comparison.inv F p' comm X,
    Comparison.inv_isHomLift F p' comm X⟩

/-- Equality of all three data components determines a pseudo-pullback morphism. -/
private theorem Comparison.hom_ext_of_components
    {X Y Z : BasedCategory C} {F₁ : X ⥤ᵇ Z} {F₂ : Y ⥤ᵇ Z}
    {P Q : (PseudoPullback F₁ F₂).obj} (f g : P ⟶ Q)
    (hbase : PseudoPullback.baseMap f = PseudoPullback.baseMap g)
    (hfst : PseudoPullback.fstMap f = PseudoPullback.fstMap g)
    (hsnd : PseudoPullback.sndMap f = PseudoPullback.sndMap g) : f = g := by
  cases f
  cases g
  cases hbase
  cases hfst
  cases hsnd
  rfl

/-- The forward and inverse fiber comparison components compose to the identity. -/
private theorem Comparison.fiber_hom_inv_id (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    Comparison.fiberHom F p' comm X ≫
      Comparison.fiberInv F p' comm X = 𝟙 _ := by
  apply Functor.Fiber.hom_ext
  apply Comparison.hom_ext_of_components
  · change 𝟙 (p.obj X.obj) ≫ 𝟙 (p.obj X.obj) = 𝟙 (p.obj X.obj)
    exact Category.id_comp _
  · change X.aut.hom ≫ X.aut.inv = 𝟙 X.obj
    exact X.aut.hom_inv_id
  · change 𝟙 X.obj ≫ 𝟙 X.obj = 𝟙 X.obj
    exact Category.id_comp _

/-- The inverse and forward fiber comparison components compose to the identity. -/
private theorem Comparison.fiber_inv_hom_id (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    Comparison.fiberInv F p' comm X ≫
      Comparison.fiberHom F p' comm X = 𝟙 _ := by
  apply Functor.Fiber.hom_ext
  apply Comparison.hom_ext_of_components
  · change 𝟙 (p.obj X.obj) ≫ 𝟙 (p.obj X.obj) = 𝟙 (p.obj X.obj)
    exact Category.id_comp _
  · change X.aut.inv ≫ X.aut.hom = 𝟙 X.obj
    exact X.aut.inv_hom_id
  · change 𝟙 X.obj ≫ 𝟙 X.obj = 𝟙 X.obj
    exact Category.id_comp _

/-- The fiber isomorphism encoded by a relative-inertia automorphism. -/
private def Comparison.iso (comm : F ⋙ p' = p) (X : RelativeInertia F) :
    ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).fiberFunctor
        (p.obj X.obj)).obj (Functor.Fiber.mk (Comparison.fiberObject_eq F X)) ≅
      ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).fiberFunctor
        (p.obj X.obj)).obj (Functor.Fiber.mk (Comparison.fiberObject_eq F X)) where
  hom := Comparison.fiberHom F p' comm X
  inv := Comparison.fiberInv F p' comm X
  hom_inv_id := Comparison.fiber_hom_inv_id F p' comm X
  inv_hom_id := Comparison.fiber_inv_hom_id F p' comm X

/-- Object owner used by the comparison functor from relative inertia to the diagonal
self-pullback. -/
private def Comparison.obj (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    (PseudoPullback (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))
      (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))).obj :=
  PseudoPullback.mk (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))
    (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)) (p.obj X.obj)
    { fst := Functor.Fiber.mk (Comparison.fiberObject_eq F X)
      snd := Functor.Fiber.mk (Comparison.fiberObject_eq F X)
      iso := Comparison.iso F p' comm X }

end RelativeInertia.Implementation

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The canonical diagonal self-intersection object attached to a relative-inertia pair.

It realizes `(A.obj, A.aut)` as the two equal diagonal legs with comparison `A.aut`.  This
bundled owner is the neutral cross-leaf API; component and functor assembly remains private in
the construction leaves. -/
@[stacks 034H "relative-inertia diagonal-comparison object"]
def RelativeInertia.diagonalComparisonObj (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj :=
  CategoryTheory.RelativeInertia.Implementation.Comparison.obj
    F.toFunctor Y.p F.w A

end BasedFunctor
end

end CategoryTheory
