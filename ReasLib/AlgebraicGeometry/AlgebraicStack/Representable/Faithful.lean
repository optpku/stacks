module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.FiberwiseEquivalence

/-!
# Faithfulness and representability of morphisms of algebraic stacks

A morphism of algebraic stacks is representable by algebraic spaces exactly when it is
faithful, equivalently when every induced fibre functor is faithful.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks over a scheme is representable by algebraic spaces
if and only if its underlying functor is faithful. -/
@[stacks 04Y5]
theorem relativelyRepresentableByAlgebraicSpaces_iff_faithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔ (toBasedFunctor f).Faithful :=
  sorry

/-- A morphism of algebraic stacks over a scheme is representable by algebraic spaces
if and only if every induced fibre functor is faithful. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff_fiberwiseFaithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ U : Over S, (fiberFunctor f U).Faithful :=
  (relativelyRepresentableByAlgebraicSpaces_iff_faithful f).trans
    (CategoryTheory.FiberedCategoryOver.Groupoids.faithful_iff_fiberwise f)

/-- A faithful morphism of algebraic stacks over a scheme is representable by
algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_of_faithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : (toBasedFunctor f).Faithful) :
    relativelyRepresentableByAlgebraicSpaces f :=
  (relativelyRepresentableByAlgebraicSpaces_iff_faithful f).mpr hf

/-- A morphism of algebraic stacks over a scheme that is faithful on every fibre
is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_of_fiberwiseFaithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hU : ∀ U : Over S, (fiberFunctor f U).Faithful) :
    relativelyRepresentableByAlgebraicSpaces f :=
  (relativelyRepresentableByAlgebraicSpaces_iff_fiberwiseFaithful f).mpr hU

end AlgebraicGeometry.AlgebraicStack
