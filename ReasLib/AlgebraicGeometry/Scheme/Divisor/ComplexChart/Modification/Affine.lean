module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CochainComplex.BerthelotOgus.Int
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- On a principal target chart, derived sections of the canonical derived eta-object are
isomorphic to the ring-level derived eta of the chart model. -/
theorem etaPullback_affineChart_isIsomorphic {X X' : Scheme.{u}}
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b]
    (C : DivisorComplexChart (D.comap b)
      ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))
    (h_principal : ∀ i : ℤ, (C.ideal i).IsPrincipal) :
    IsIsomorphic
      ((Derived.functor
        ⟨C.generator, C.regular⟩).obj (DerivedCategory.Q.obj C.model))
      ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace C.U).obj
        ((functor (D.comap b).toSubobject).obj
          ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
