module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Integral

@[expose] public section

noncomputable section

universe u

/- Proposition 41.20.6: For a surjective integral morphism `f : X ⟶ S`, the canonical
functor from quasi-compact separated schemes étale over `S` to étale descent data relative
to `X / S` with quasi-compact separated component is an equivalence. -/
@[stacks 0BTP] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.qcSeparatedIsEquivalence :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.IsIntegralHom f],
      CategoryTheory.Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.qcSeparated f))
