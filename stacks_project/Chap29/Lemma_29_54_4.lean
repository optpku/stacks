module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.FiniteComponents

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 29.54.4
If every quasi-compact open of a scheme has finitely many irreducible
components, then at every point the normalization pushforward stalk is
canonically isomorphic as a local-ring algebra to the integral closure in the
total quotient ring of the reduced local ring.
-/
@[stacks 0C3B] #check
  (AlgebraicGeometry.Scheme.Normalization.Stalk.pushforward_exists_ringEquiv_reducedIntegralClosure :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X),
      ∃ e : AlgebraicGeometry.Scheme.Normalization.Stalk.pushforward X x ≃+*
          AlgebraicGeometry.Scheme.Normalization.Stalk.reducedIntegralClosure X x,
        e.toRingHom.comp
            (AlgebraicGeometry.Scheme.Normalization.Stalk.pushforwardMap X x) =
          algebraMap (X.presheaf.stalk x)
            (AlgebraicGeometry.Scheme.Normalization.Stalk.reducedIntegralClosure X x))

#check
  (AlgebraicGeometry.Scheme.Normalization.Stalk.reducedIntegralClosure_exists_ringEquiv_piResidueFields :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X),
      ∃ e : AlgebraicGeometry.Scheme.Normalization.Stalk.reducedIntegralClosure X x ≃+*
          integralClosure (X.presheaf.stalk x)
            ((q : minimalPrimes (X.presheaf.stalk x)) → q.1.ResidueField),
        e.toRingHom.comp
            (algebraMap (X.presheaf.stalk x)
              (AlgebraicGeometry.Scheme.Normalization.Stalk.reducedIntegralClosure X x)) =
          algebraMap (X.presheaf.stalk x)
            (integralClosure (X.presheaf.stalk x)
              ((q : minimalPrimes (X.presheaf.stalk x)) → q.1.ResidueField)))

#check
  (AlgebraicGeometry.Scheme.stalk_finite_minimalPrimes :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X),
      (minimalPrimes (X.presheaf.stalk x)).Finite)
