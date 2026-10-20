/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.FiberPair
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Setoids

/-!
# A fiberwise criterion for morphisms representable by algebraic spaces

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces exactly when it is faithful on every fibre
and every fiber-pair isomorphism-class presheaf is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces if and only if every fibre functor is faithful
and every fiber-pair isomorphism-class presheaf, transported along the iterated
slice equivalence, is an algebraic space over its test scheme. -/
@[stacks 02ZY]
theorem relativelyRepresentableByAlgebraicSpaces.iff_fiberwise
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      (∀ U : Over S, (fiberFunctor f U).Faithful) ∧
        Hom.fiberPairClasses.isAlgebraicSpace f :=
  sorry

/-- A 1-morphism representable by algebraic spaces is faithful on every fibre. -/
theorem relativelyRepresentableByAlgebraicSpaces.fiberwiseFaithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) (U : Over S) :
    (fiberFunctor f U).Faithful :=
  sorry

/-- A 1-morphism representable by algebraic spaces has algebraic-space
fiber-pair presheaves. -/
theorem relativelyRepresentableByAlgebraicSpaces.fiberPairs
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Hom.fiberPairClasses.isAlgebraicSpace f :=
  sorry

/-- Fiberwise faithfulness and algebraic-space fiber-pair presheaves imply
relative representability by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_fiberwiseFaithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hFaithful : ∀ U : Over S, (fiberFunctor f U).Faithful)
    (hPairs : Hom.fiberPairClasses.isAlgebraicSpace f) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry
