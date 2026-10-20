module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalGlueing

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 81.10.10. In Situation 81.10.6, derived pushforward induces an equivalence
between the quasi-coherent derived categories supported on the inverse image of
the closed subspace and on the closed subspace, with derived pullback as quasi-inverse. -/
@[stacks 0AFJ] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.pushforward_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
      [IsFormalGlueing f i],
      (DerivedQCoh.SupportedOn.pushforward f i).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.pullback_isQuasiInverse :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i],
    (DerivedQCoh.SupportedOn.pushforward f i).IsQuasiInverse
      (DerivedQCoh.SupportedOn.pullback f i))
