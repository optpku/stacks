/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.LocallyFree

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- If a perfect derived module has a locally bounded termwise finite locally free
representative, then its canonical derived eta-pullback along a good-triple modification has
a globally bounded termwise finite locally free representative. -/
theorem existsBoundedEtaPullbackRepresentative {X X' : Scheme.{u}}
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b]
    (hrep : ∃ P : CochainComplex X.toRingedSpace.Modules ℤ,
      IsIsomorphic (DerivedCategory.Q.obj P) M ∧
        RingedSpace.CochainComplex.IsLocallyBoundedAbove P ∧
        RingedSpace.CochainComplex.IsLocallyBoundedBelow P ∧
        ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (P.X i)) :
    ∃ Q : CochainComplex X'.toRingedSpace.Modules ℤ,
      IsIsomorphic (DerivedCategory.Q.obj Q)
          ((Eta.Derived.functor (D.comap b).toSubobject).obj
            ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)) ∧
        _root_.CochainComplex.bounded X'.toRingedSpace.Modules Q ∧
        ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (Q.X i) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
