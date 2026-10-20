module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Coproduct
import StacksCheckRecall

/-!
# Lemma 29.44.13

A finite coproduct of finite morphisms is finite.

@stack 0CYI
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.44.13

For a finite family of finite morphisms of schemes with a common target, the morphism from
their coproduct to that target is finite.
-/
@[stacks 0CYI] #check (AlgebraicGeometry.finite_sigma_desc :
  ∀ {ι : Type u} {X : ι → AlgebraicGeometry.Scheme.{u}}
    {Y : AlgebraicGeometry.Scheme.{u}} (f : ∀ i, X i ⟶ Y) [Finite ι],
    (∀ i, AlgebraicGeometry.IsFinite (f i)) →
      AlgebraicGeometry.IsFinite (CategoryTheory.Limits.Sigma.desc f))
