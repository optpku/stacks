/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.ToSetoidsFiber

/-!
# Associated categories fibred in sets

This leaf realizes the fiberwise isomorphism-class presheaf as a category
fibred in sets and exposes its choice-free fiber equivalences.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite
open CategoryOfElements
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

/-- The category fibred in sets canonically associated to `Z`: the category of elements of the
presheaf `U ↦` isomorphism classes of objects of `Z.p.Fiber U`. -/
@[stacks 0045 "associated category fibred in sets"]
noncomputable def associatedSets
    (Z : FiberedCategoryOver.Setoids C) : FiberedCategoryOver.Sets C :=
  (FiberedCategoryOver.Sets.ofPresheaf C).obj
    (Functor.fiberIsoClassPresheaf Z.p)

/-- The projection of `associatedSets` is the opposite category-of-elements projection for the
fiberwise-isomorphism-class presheaf. -/
@[simp, stacks 0045 "associated-sets projection"]
theorem associatedSets.p (Z : FiberedCategoryOver.Setoids C) :
    Z.associatedSets.p =
      (CategoryOfElements.π (Functor.fiberIsoClassPresheaf Z.p)).leftOp := sorry
/- Proof strategy: unfold `associatedSets` and use `FiberedCategoryOver.Sets.ofFunctor.p`. -/

/-- The total category of `associatedSets` is the opposite category of elements of the
fiberwise-isomorphism-class presheaf. -/
@[simp, stacks 0045 "associated-sets total category"]
theorem associatedSets.total (Z : FiberedCategoryOver.Setoids C) :
    Z.associatedSets.total =
      (Functor.fiberIsoClassPresheaf Z.p).Elementsᵒᵖ := sorry
/- Proof strategy: unfold `associatedSets` and apply `FiberedCategoryOver.Sets.ofPresheaf.obj.total`.
This exposes the canonical category-of-elements carrier without unfolding the full-subcategory
implementation of categories fibred in sets. -/

/-- The standard fiber of `associatedSets` over `U` is canonically the type of isomorphism
classes in the standard fiber of `Z` over `U`.

Both directions are the explicit category-of-elements evaluation and tautological value-to-fiber
maps from the discrete Grothendieck construction; in particular this equivalence does not select
representatives of isomorphism classes. -/
@[stacks 0045 "associated-sets fiber equivalence"]
noncomputable def associatedSets.fiberEquiv
    (Z : FiberedCategoryOver.Setoids C) (U : C) :
    Z.associatedSets.p.Fiber U ≃
      (Functor.fiberIsoClassPresheaf Z.p).obj (op U) :=
  FiberedCategoryOver.Sets.ofPresheaf.fiberEquiv
    (Functor.fiberIsoClassPresheaf Z.p) U
/- Axiom audit: the forward and inverse functions are the explicit functions of
`ofPresheaf.fiberEquiv`. Any `sorryAx` dependency is confined to their Prop-valued inverse-law
fields. No representative of a quotient class is chosen. -/

/-- The forward direction of `associatedSets.fiberEquiv` evaluates a fiber object as its stored
fiberwise isomorphism class. -/
@[simp, stacks 0045 "associated-sets fiber equivalence forward computation"]
theorem associatedSets.fiberEquiv.apply
    (Z : FiberedCategoryOver.Setoids C) (U : C) (x : Z.associatedSets.p.Fiber U) :
    associatedSets.fiberEquiv Z U x =
      FiberedCategoryOver.Sets.ofPresheaf.fiberToValue
        (Functor.fiberIsoClassPresheaf Z.p) U x := sorry
/- Proof strategy: unfold `associatedSets.fiberEquiv` and apply
`FiberedCategoryOver.Sets.ofPresheaf.fiberEquiv.apply`. -/

/-- The inverse direction of `associatedSets.fiberEquiv` places a fiberwise isomorphism class in
the tautological standard fiber of the associated category of elements. -/
@[simp, stacks 0045 "associated-sets fiber equivalence inverse computation"]
theorem associatedSets.fiberEquiv.symm_apply
    (Z : FiberedCategoryOver.Setoids C) (U : C)
    (x : (Functor.fiberIsoClassPresheaf Z.p).obj (op U)) :
    (associatedSets.fiberEquiv Z U).symm x =
      FiberedCategoryOver.Sets.ofPresheaf.valueToFiber
        (Functor.fiberIsoClassPresheaf Z.p) U x := sorry
/- Proof strategy: unfold `associatedSets.fiberEquiv` and apply
`FiberedCategoryOver.Sets.ofPresheaf.fiberEquiv.symm_apply`. -/

/-- Straightening the associated category fibred in sets recovers the fiberwise
isomorphism-class presheaf of `Z`. -/
@[stacks 0045 "associated-sets presheaf comparison"]
noncomputable def associatedSets.toPresheafIso
    (Z : FiberedCategoryOver.Setoids C) :
    (FiberedCategoryOver.Sets.toPresheaf C).obj Z.associatedSets ≅
      Functor.fiberIsoClassPresheaf Z.p :=
  FiberedCategoryOver.Sets.PresheafEquivalence.toObjIso
    (Functor.fiberIsoClassPresheaf Z.p)
/- Axiom audit: this is the explicit discrete Grothendieck comparison for the concrete
presheaf `Functor.fiberIsoClassPresheaf Z.p`; its non-`Prop` components are the
fiber-value maps. -/

/-- The forward component of `associatedSets.toPresheafIso` is the standard
`associatedSets.fiberEquiv`. -/
@[simp, stacks 0045 "associated-sets presheaf comparison forward component"]
theorem associatedSets.toPresheafIso.hom.app
    (Z : FiberedCategoryOver.Setoids C) (U : Cᵒᵖ) :
    (associatedSets.toPresheafIso Z).hom.app U =
      (Equiv.toIso (associatedSets.fiberEquiv Z (unop U))).hom := sorry
/- Proof strategy: apply `PresheafEquivalence.toObjIso.hom.app` to the fiberwise
isomorphism-class presheaf. -/

/-- The inverse component of `associatedSets.toPresheafIso` is the inverse
`associatedSets.fiberEquiv`. -/
@[simp, stacks 0045 "associated-sets presheaf comparison inverse component"]
theorem associatedSets.toPresheafIso.inv.app
    (Z : FiberedCategoryOver.Setoids C) (U : Cᵒᵖ) :
    (associatedSets.toPresheafIso Z).inv.app U =
      (Equiv.toIso (associatedSets.fiberEquiv Z (unop U))).inv := sorry
/- Proof strategy: apply `PresheafEquivalence.toObjIso.inv.app` to the fiberwise
isomorphism-class presheaf. -/

/-- The fiber equivalences for `associatedSets` commute with restriction in the base. -/
@[stacks 0045 "associated-sets fiber equivalence naturality"]
theorem associatedSets.fiberEquiv.naturality
    (Z : FiberedCategoryOver.Setoids C) {U V : Cᵒᵖ} (f : U ⟶ V) :
    Z.associatedSets.p.fiberObjectPresheaf.map f ≫
        (Equiv.toIso (associatedSets.fiberEquiv Z (unop V))).hom =
      (Equiv.toIso (associatedSets.fiberEquiv Z (unop U))).hom ≫
        (Functor.fiberIsoClassPresheaf Z.p).map f := sorry
/- Proof strategy: specialize `FiberedCategoryOver.Sets.ofPresheaf.fiberEquiv.naturality` to
`Functor.fiberIsoClassPresheaf Z.p`, using the definition of `associatedSets` and
`FiberedCategoryOver.Sets.toPresheaf.obj` on the left. -/

end FiberedCategoryOver.Setoids

end CategoryTheory
