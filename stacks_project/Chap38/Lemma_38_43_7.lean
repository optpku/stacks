module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

/- Lemma 38.43.7: for a good-triple modification `b`, derived ideal-sheaf eta along
`D.comap b` sends the derived pullback of `M` to a perfect object on the source scheme. -/
@[stacks 0F8U] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_isPerfect :
    ∀ {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b],
    RingedSpace.ModuleDerived.IsPerfect
      ((Eta.Derived.functor (D.comap b).toSubobject).obj
        ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)))
