module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.17.4: for a closed immersion `i : X ⟶ Y` in
`Scheme.FiniteTypeSeparatedOver S`, upper shriek along `i` is naturally isomorphic to
derived internal Hom from `𝒪_X`. -/
@[stacks 0AA2]
#check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionUpperShriek_isomorphic_internalHom :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeSeparatedOver S} (i : X ⟶ Y)
      [IsClosedImmersion i.hom.left],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjointPlus i.hom.left
          (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
            i.hom.left).rightAdjoint
          (Adjunction.ofIsLeftAdjoint
            (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn i.hom.left)))
        (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomPlus i.hom.left))
