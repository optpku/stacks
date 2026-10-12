/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom
public import ReasLib.CategoryTheory.Fibered.BasedCategory.CategoryOfElements

/-!
# Comparison with associated sets

This leaf owns the explicit comparison from a category fibred in setoids to
the setoid image of its associated category fibred in sets.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite
open CategoryOfElements
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

/-- The canonical comparison from a category fibred in setoids to the setoid image of its
associated category fibred in sets. -/
@[stacks 0045 "associated-sets comparison"]
noncomputable def toAssociatedSets
    (Z : FiberedCategoryOver.Setoids C) :
    Z ⟶ (FiberedCategoryOver.Sets.toSetoids C).obj Z.associatedSets :=
  ofBasedFunctor <|
    CategoryOfElements.Section.basedFunctor Z.toBasedCategory
      (Functor.fiberIsoClassPresheaf Z.p)
      (Functor.fiberIsoClassPresheaf.tautologicalSection Z.p)
/- Data audit: the comparison is generated from the explicit tautological fiber-class section by
the neutral category-of-elements construction. `sorryAx` can enter only through naturality,
functor laws, strict-base equations, and owner proofs. -/

/-- The standard fiber of the setoid-fibred target of `toAssociatedSets` is canonically the type
of isomorphism classes in the corresponding fiber of `Z`.

The first factor only transports through the full-subcategory inclusion `Sets.toSetoids`; the
second is the choice-free category-of-elements equivalence `associatedSets.fiberEquiv`. -/
@[stacks 0045 "associated-sets target-fibre equivalence"]
noncomputable def toAssociatedSets.targetFiberEquiv
    (Z : FiberedCategoryOver.Setoids C) (U : C) :
    ((FiberedCategoryOver.Sets.toSetoids C).obj Z.associatedSets).toBasedCategory.p.Fiber U ≃
      (Functor.fiberIsoClassPresheaf Z.p).obj (op U) :=
  (FiberedCategoryOver.Sets.toSetoids.fiberEquiv Z.associatedSets U).trans
    (associatedSets.fiberEquiv Z U)
/- Axiom audit: both component equivalences are explicit transport or category-of-elements data.
Neither direction chooses a representative of an isomorphism class. -/

/-- The forward map of `toAssociatedSets.targetFiberEquiv` first forgets the set-valued owner
property by transport and then evaluates the associated category-of-elements fiber. -/
@[simp, stacks 0045 "associated-sets target fiber equivalence forward computation"]
theorem toAssociatedSets.targetFiberEquiv.apply
    (Z : FiberedCategoryOver.Setoids C) (U : C)
    (x : ((FiberedCategoryOver.Sets.toSetoids C).obj Z.associatedSets).toBasedCategory.p.Fiber U) :
    toAssociatedSets.targetFiberEquiv Z U x =
      associatedSets.fiberEquiv Z U
        (FiberedCategoryOver.Sets.toSetoids.fiberEquiv Z.associatedSets U x) := sorry
/- Proof strategy: unfold the forward function of the transitive equivalence. -/

/-- The inverse map of `toAssociatedSets.targetFiberEquiv` first returns to the associated
category-of-elements fiber and then transports back through `toSetoids`. -/
@[simp, stacks 0045 "associated-sets target fiber equivalence inverse computation"]
theorem toAssociatedSets.targetFiberEquiv.symm_apply
    (Z : FiberedCategoryOver.Setoids C) (U : C)
    (x : (Functor.fiberIsoClassPresheaf Z.p).obj (op U)) :
    (toAssociatedSets.targetFiberEquiv Z U).symm x =
      (FiberedCategoryOver.Sets.toSetoids.fiberEquiv Z.associatedSets U).symm
        ((associatedSets.fiberEquiv Z U).symm x) := sorry
/- Proof strategy: unfold the inverse function of the transitive equivalence. -/

/-- The target-fiber equivalences for `toAssociatedSets` commute with restriction in the base. -/
@[stacks 0045 "associated-sets target fiber equivalence naturality"]
theorem toAssociatedSets.targetFiberEquiv.naturality
    (Z : FiberedCategoryOver.Setoids C) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (((FiberedCategoryOver.Sets.toSetoids C).obj
        Z.associatedSets).toBasedCategory.p.fiberObjectPresheaf).map f ≫
        (Equiv.toIso (toAssociatedSets.targetFiberEquiv Z (unop V))).hom =
      (Equiv.toIso (toAssociatedSets.targetFiberEquiv Z (unop U))).hom ≫
        (Functor.fiberIsoClassPresheaf Z.p).map f := sorry
/- Proof strategy: compose `toSetoids.fiberEquiv.naturality Z.associatedSets f` with
`associatedSets.fiberEquiv.naturality Z f` and reassociate the component isomorphisms. -/

/-- On objects, the comparison remembers the represented fiberwise isomorphism class. -/
@[simp, stacks 0045 "associated-sets comparison object computation"]
theorem toAssociatedSets.obj.unop
    (Z : FiberedCategoryOver.Setoids C) (a : Z.total) :
    unop ((FiberedCategoryOver.Setoids.toFunctor Z.toAssociatedSets).obj a) =
      (Functor.fiberIsoClassPresheaf Z.p).elementsMk (op (Z.p.obj a))
        (Quotient.mk'' ⟨a, rfl⟩) := sorry

/-- On morphisms, the comparison projects to the opposite original base map. -/
@[simp, stacks 0045 "associated-sets comparison opposite projection"]
theorem toAssociatedSets.map.unop_projection
    (Z : FiberedCategoryOver.Setoids C) {a b : Z.total} (φ : a ⟶ b) :
    (CategoryOfElements.π (Functor.fiberIsoClassPresheaf Z.p)).map
        ((FiberedCategoryOver.Setoids.toFunctor Z.toAssociatedSets).map φ).unop =
      (Z.p.map φ).op := sorry

/-- The comparison sends a total morphism to an arrow over its original base morphism. -/
@[simp, stacks 0045 "associated-sets comparison projection"]
theorem toAssociatedSets.map.projection
    (Z : FiberedCategoryOver.Setoids C) {a b : Z.total} (φ : a ⟶ b) :
    Z.associatedSets.p.map
        ((FiberedCategoryOver.Setoids.toFunctor Z.toAssociatedSets).map φ) =
      Z.p.map φ := sorry

/-- Fiberwise, the comparison sends an object to its isomorphism class without selecting a
representative. -/
@[simp, stacks 0045 "associated-sets comparison fiber computation"]
theorem toAssociatedSets.fiberFunctor.apply
    (Z : FiberedCategoryOver.Setoids C) (U : C) (x : Z.p.Fiber U) :
    toAssociatedSets.targetFiberEquiv Z U
        ((FiberedCategoryOver.Setoids.fiberFunctor Z.toAssociatedSets U).obj x) =
      Quotient.mk'' x := sorry

/-- The map on isomorphism classes induced by the comparison is the specified inverse of the
choice-free target-fiber equivalence. -/
@[stacks 0045 "associated-sets comparison fiber class map"]
theorem toAssociatedSets.fiberFunctor.isoClassesToObj
    (Z : FiberedCategoryOver.Setoids C) (U : C) :
    (FiberedCategoryOver.Setoids.fiberFunctor Z.toAssociatedSets U).isoClassesToObj =
      (toAssociatedSets.targetFiberEquiv Z U).symm := sorry

/-- The quotient-level fiber map induced by `toAssociatedSets` is bijective. -/
@[stacks 0045 "associated-sets comparison fiber bijection"]
theorem toAssociatedSets.fiberFunctor.isoClassesToObj.bijective
    (Z : FiberedCategoryOver.Setoids C) (U : C) :
    Function.Bijective
      (FiberedCategoryOver.Setoids.fiberFunctor Z.toAssociatedSets U).isoClassesToObj := sorry

/-- The comparison is the forward morphism of an equivalence between the underlying based
categories. -/
@[stacks 0045 "associated-sets comparison is an equivalence"]
theorem toAssociatedSets.exists_equivalence
    (Z : FiberedCategoryOver.Setoids C) :
    ∃ e : Z.toBasedCategory ≌ Z.associatedSets.toBasedCategory,
      e.hom = FiberedCategoryOver.Setoids.toBasedFunctor Z.toAssociatedSets := sorry

/-- Heterogeneous compatibility projection of `toAssociatedSets.exists_equivalence`. -/
@[stacks 0045 "associated-sets comparison equivalence instance"]
instance toAssociatedSets.isEquivalence
    (Z : FiberedCategoryOver.Setoids C) :
    BasedFunctor.IsEquivalence
      (FiberedCategoryOver.Setoids.toBasedFunctor Z.toAssociatedSets) := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
