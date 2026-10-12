/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.EtaFlattening

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/- Lemma 38.43.11: for a good-triple modification `b`, the divisor `D' = D.comap b`
contains a finitely presented closed subscheme containing its inverse image of the maximal
finite-free open of `M`. The pullback of the η-complex to this subscheme has finite locally
free cohomology whose stalk ranks agree with those of `M` over that open. -/
@[stacks 0F8X] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.existsEtaFlattening :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      (hM : RingedSpace.ModuleDerived.IsPerfect M) → (b : X' ⟶ X) →
      [IsGoodTripleModification D M b] →
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
                  (M.cohomologyStalk n ((J.subschemeι ≫ D'.subschemeι ≫ b) t)))

end AlgebraicGeometry.Scheme.IsGoodTripleModification
