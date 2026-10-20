module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Adjunction
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Derived étale restriction–pushforward adjunction

An étale morphism `f : V ⟶ X` of algebraic spaces induces `f^* ⊣ Rf_*` on unbounded
derived categories of modules. Restriction is exact, so the left adjoint is
`restrictFunctorDerived`; the right adjoint is the K-injective derived pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictPushforwardDerivedAdjunction :
  ∀ {S : Scheme.{u}} {V X : AlgebraicSpace S} (f : V ⟶ X) [Etale f],
    restrictFunctorDerived f ⊣ moduleDerivedPushforward f)
