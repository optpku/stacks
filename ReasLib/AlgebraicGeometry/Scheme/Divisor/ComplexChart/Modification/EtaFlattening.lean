module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.EtaFlattening
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.FiniteFreeLocus
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- For a good-triple modification `b`, the pulled-back divisor contains a finitely
presented closed subscheme containing the inverse image of the maximal finite-free open.
On this subscheme, the pulled-back derived eta-complex has finite locally free cohomology,
whose stalk ranks agree with those of the original complex over that open. -/
@[stacks 0F8X]
theorem existsEtaFlattening {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] :
    let D' := D.comap b
    let M' := (RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M
    let Q := (functor D'.toSubobject).obj M'
    let W := hM.finiteFreeOpen (fun x ↦ inferInstance)
    ∃ J : D'.subscheme.IdealSheafData, let T := J.subscheme;
      Scheme.Hom.FinitePresentation J.subschemeι ∧
        J ≤ (((D'.subschemeι ≫ b) ⁻¹ᵁ W).ι).ker ∧
        finiteLocallyFreeOn
          ((RingedSpace.modulePullbackDerived
            (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) ⊤ ∧
        ∀ (n : ℤ) (t : T),
          (J.subschemeι ≫ D'.subschemeι ≫ b) t ∈ W →
            Module.rank (T.presheaf.stalk t)
                (cohomologyStalk ((RingedSpace.modulePullbackDerived
                  (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) n t) =
              Module.rank (X.presheaf.stalk ((J.subschemeι ≫ D'.subschemeι ≫ b) t))
                (M.cohomologyStalk n ((J.subschemeι ≫ D'.subschemeι ≫ b) t)) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
