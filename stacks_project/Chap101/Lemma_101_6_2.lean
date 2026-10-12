/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Construction
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap101.«101_5_2_1_RelativeIsom»

/-!
# Second diagonal of morphisms of algebraic stacks

A morphism of algebraic stacks is representable by algebraic spaces if and
only if its second diagonal is an equivalence, equivalently if relative
inertia is trivial via the identity section, equivalently if the kernel of
each `Isom` comparison is trivial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open Hom.diagonal (relativeIsom)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.6.2: Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `f` is representable by algebraic spaces; the
second diagonal `Hom.diagonal (Hom.diagonal f)` is an isomorphism of stacks;
the group stack `I_{X/Y}` is trivial over `X`, i.e. the identity section
`RelativeInertia.identitySection f` is an equivalence; and for a scheme `T`
and an object `x` of `X` over `T`, the kernel of
`Isom_X(x, x) ⟶ Isom_Y(f(x), f(x))` is trivial. -/
@[stacks 04YY]
theorem relativelyRepresentableByAlgebraicSpaces_tfae {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    List.TFAE
      [relativelyRepresentableByAlgebraicSpaces f,
        BasedFunctor.IsEquivalence
          (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1}
            (Hom.diagonal.{u + 1, u, u + 1} f))),
        BasedFunctor.IsEquivalence
          (toBasedFunctor (RelativeInertia.identitySection.{u + 1, u, u, u + 1} f)),
        ∀ {T : Over S} (x : X.p.Fiber T) (T' : Over T),
          ∃ φ : (relativeIsom f x).obj (op T'), ∀ ψ, ψ = φ] :=
  sorry

/-- A morphism of algebraic stacks is representable by algebraic spaces if and
only if its second diagonal is an equivalence over the base. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff_isEquivalence_secondDiagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      BasedFunctor.IsEquivalence
        (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1}
          (Hom.diagonal.{u + 1, u, u + 1} f))) :=
  sorry

/-- A morphism of algebraic stacks is representable by algebraic spaces if and
only if the relative-inertia identity section is an equivalence over the
base. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff_isEquivalence_identitySection
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      BasedFunctor.IsEquivalence
        (toBasedFunctor
          (RelativeInertia.identitySection.{u + 1, u, u, u + 1} f)) :=
  sorry

/-- A morphism of algebraic stacks is representable by algebraic spaces if and
only if for every scheme `T` and object `x` of `X` over `T`, the kernel sheaf
`relativeIsom f x` has exactly one section over every `T'`. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff_unique_relativeIsom
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ {T : Over S} (x : X.p.Fiber T) (T' : Over T),
        ∃ φ : (relativeIsom f x).obj (op T'), ∀ ψ, ψ = φ :=
  sorry

end AlgebraicGeometry.AlgebraicStack
