module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Étale algebraic spaces over a field

An algebraic space étale over the spectrum of a field is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Lemma 66.16.8: if `S` is a scheme, `k` is a field, and `X ⟶ Spec (CommRingCat.of k)` is an
étale morphism of algebraic spaces over `S`, then `X` is a scheme. This fails for étale morphisms
towards a general scheme. -/
@[stacks 03KX]
theorem of_etale_over_field {S : Scheme.{u}} {k : Type u} [Field k] {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : X ⟶ ofOver (Over.mk σ)) [Etale f] :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
