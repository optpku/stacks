/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Theorem 41.14.1: For a scheme morphism `f`, the conditions that `f` is an open
immersion, universally injective and étale, or a flat monomorphism locally of finite
presentation are equivalent. -/
@[stacks 025G] #check (AlgebraicGeometry.tfae_openImmersion :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    List.TFAE [
      AlgebraicGeometry.IsOpenImmersion f,
      AlgebraicGeometry.UniversallyInjective f ∧ AlgebraicGeometry.Etale f,
      AlgebraicGeometry.Flat f ∧ Mono f ∧
        AlgebraicGeometry.LocallyOfFinitePresentation f])
