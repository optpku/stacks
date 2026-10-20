/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open Hom.diagonal (relativeIsom)
open scoped Bicategory

universe u

/- Lemma 101.6.2: Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `f` is representable by algebraic spaces; the
second diagonal `Hom.diagonal (Hom.diagonal f)` is an isomorphism of stacks;
the group stack `I_{X/Y}` is trivial over `X`, i.e. the identity section
`RelativeInertia.identitySection f` is an equivalence; and for a scheme `T`
and an object `x` of `X` over `T`, the kernel of
`Isom_X(x, x) ⟶ Isom_Y(f(x), f(x))` is trivial. -/
@[stacks 04YY] #check (AlgebraicGeometry.AlgebraicStack.Representable.tfae :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    List.TFAE
      [relativelyRepresentableByAlgebraicSpaces f,
        BasedFunctor.IsEquivalence
          (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1}
            (Hom.diagonal.{u + 1, u, u + 1} f))),
        BasedFunctor.IsEquivalence
          (toBasedFunctor (RelativeInertia.identitySection.{u + 1, u, u, u + 1} f)),
        ∀ {T : Over S} (x : X.p.Fiber T) (T' : Over T),
          ∃ φ : (relativeIsom f x).obj (op T'), ∀ ψ, ψ = φ])

#check (AlgebraicGeometry.AlgebraicStack.Representable.iff_secondDiagonal :
    ∀
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces f ↔
      BasedFunctor.IsEquivalence
        (toBasedFunctor (Hom.diagonal.{u + 1, u, u + 1}
          (Hom.diagonal.{u + 1, u, u + 1} f))))

#check (AlgebraicGeometry.AlgebraicStack.Representable.iff_identitySection :
    ∀
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces f ↔
      BasedFunctor.IsEquivalence
        (toBasedFunctor
          (RelativeInertia.identitySection.{u + 1, u, u, u + 1} f)))

#check (AlgebraicGeometry.AlgebraicStack.Representable.iff_unique_relativeIsom :
    ∀
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ {T : Over S} (x : X.p.Fiber T) (T' : Over T),
        ∃ φ : (relativeIsom f x).obj (op T'), ∀ ψ, ψ = φ)
