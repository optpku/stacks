module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Field

/-!
# Étale algebraic spaces over a field

An algebraic space étale over the spectrum of a field is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.16.8: if `S` is a scheme, `k` is a field, and `X ⟶ Spec (CommRingCat.of k)` is an
étale morphism of algebraic spaces over `S`, then `X` is a scheme. This fails for étale morphisms
towards a general scheme. -/
@[stacks 03KX] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_etale_over_field :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] {X : AlgebraicSpace S}
      (σ : Spec (CommRingCat.of k) ⟶ S)
      (f : X ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk σ))
      [AlgebraicGeometry.AlgebraicSpace.Etale f],
      AlgebraicGeometry.AlgebraicSpace.IsScheme X)
