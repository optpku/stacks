/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Monomorphism
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]

/- Exercise 111.65.5 (Monomorphisms): a monomorphism of schemes is injective
on points. -/
@[stacks 0GYD] #check (AlgebraicGeometry.Scheme.Hom.injectiveOfMono :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f], Function.Injective f)

#check (inferInstance : UniversallyInjective f)
