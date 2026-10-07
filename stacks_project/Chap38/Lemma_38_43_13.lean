module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.LocallyFree

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

/- Lemma 38.43.13: a locally bounded termwise finite locally free representative of `M`
gives such a representative for the eta-derived pullback along a good-triple modification. -/
@[stacks 0GU0] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_hasLocallyBoundedFiniteLocallyFreeRepresentative :
    ∀ {X X' : Scheme.{u}} (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι]
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b]
      (hrep : ∃ P : CochainComplex X.toRingedSpace.Modules ℤ,
        IsIsomorphic (DerivedCategory.Q.obj P) M ∧
          RingedSpace.CochainComplex.IsLocallyBoundedAbove P ∧
          RingedSpace.CochainComplex.IsLocallyBoundedBelow P ∧
          ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (P.X i)),
      ∃ Q : CochainComplex X'.toRingedSpace.Modules ℤ,
        IsIsomorphic (DerivedCategory.Q.obj Q)
            ((Eta.Derived.functor (D.comap b).toSubobject).obj
              ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)) ∧
          RingedSpace.CochainComplex.IsLocallyBoundedAbove Q ∧
          RingedSpace.CochainComplex.IsLocallyBoundedBelow Q ∧
          ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (Q.X i))
