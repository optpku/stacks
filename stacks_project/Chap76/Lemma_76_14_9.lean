/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Characterization
import StacksCheckRecall

/-!
# Closed immersions of algebraic spaces

A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed and unramified together with either a monomorphism or
universal injectivity, and if and only if it is universally closed and locally
of finite type together with either a monomorphism or the formally unramified
universally injective package.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.14.9: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is a closed
immersion; `f` is universally closed, unramified, and a monomorphism; `f` is
universally closed, unramified, and universally injective; `f` is universally
closed, locally of finite type, and a monomorphism; `f` is universally closed,
universally injective, locally of finite type, and formally unramified. -/
@[stacks 05W8] #check (AlgebraicGeometry.AlgebraicSpace.tfae_isClosedImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [
      IsClosedImmersion f,
      UniversallyClosed f ∧ Unramified f ∧ Mono f,
      UniversallyClosed f ∧ Unramified f ∧ UniversallyInjective f,
      UniversallyClosed f ∧ LocallyOfFiniteType f ∧ Mono f,
      UniversallyClosed f ∧ UniversallyInjective f ∧ LocallyOfFiniteType f ∧
        FormallyUnramified f])
