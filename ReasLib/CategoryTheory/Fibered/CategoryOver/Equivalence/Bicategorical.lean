/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Equivalence
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Action
public import ReasLib.CategoryTheory.Fibered.Equivalence.StronglyCartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bicategorical equivalences of fibred categories

This module packages an equivalence of the underlying based functor as an equivalence in
`FiberedCategoryOver`. The inverse of a based equivalence preserves strongly cartesian arrows,
so both directions satisfy the hom property of the locally induced bicategory.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- Package an explicit proof that the underlying based functor is an equivalence as a
bicategorical equivalence of fibred categories. -/
noncomputable def asEquivalenceOf
    (F : X ⟶ Y) (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    X ≌ Y :=
  let e := (FiberedCategoryOver.toBasedFunctor F).asEquivalenceOf hF
  Bicategory.LocallyInducedBicategory.equivalenceMk e
    (BasedFunctor.IsEquivalence.preservesStronglyCartesian e.hom)
    (BasedFunctor.IsEquivalence.preservesStronglyCartesian e.inv)

/-- The forward morphism of `asEquivalenceOf F hF` is the original fibred morphism. -/
@[simp]
theorem asEquivalenceOf.hom
    (F : X ⟶ Y) (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    (asEquivalenceOf F hF).hom = F := sorry

namespace IsEquivalence

/-- Fixed-forward-morphism equivalence data for a fibred morphism whose underlying based functor
is an equivalence. -/
noncomputable def toOnHom
    {F : X ⟶ Y} (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    Bicategory.Equivalence.OnHom F :=
  Bicategory.Equivalence.OnHom.ofEquivalence (asEquivalenceOf F hF)

/-- Reassembling the fixed-forward-morphism data gives the canonical fibred equivalence. -/
@[simp]
theorem toOnHom.toEquivalence
    {F : X ⟶ Y} (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    (toOnHom hF).toEquivalence = asEquivalenceOf F hF := sorry

/-- Bicategorical equivalence data on a fibred morphism imply equivalence of its underlying
based functor. -/
theorem ofOnHom {F : X ⟶ Y} (hF : Bicategory.Equivalence.OnHom F) :
    (FiberedCategoryOver.toBasedFunctor F).IsEquivalence := sorry

end IsEquivalence

/- Data audit: the based equivalence owns the inverse, unit, and counit. The existing generic
equivalence theorem supplies strongly-cartesian preservation in both directions;
`equivalenceMk` retains all non-Prop equivalence data unchanged. -/

end FiberedCategoryOver.Hom

end CategoryTheory
