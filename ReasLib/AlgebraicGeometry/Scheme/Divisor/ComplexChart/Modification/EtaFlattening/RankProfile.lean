module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.EtaFlattening
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Cohomology.RankProfile

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- For a good-triple modification and an integer cohomological rank profile, a chosen
η-flattening subscheme contains a clopen open on which the η-pullback has that rank profile,
and the inverse image of the maximal rank-profile open factors through this clopen open. -/
@[stacks 0F8Y]
theorem existsClopenEtaRankProfile {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] (ρ : ℤ → ℤ) :
    let D' := D.comap b
    let M' := (RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M
    let Q := (functor D'.toSubobject).obj M'
    let Wₑ := hM.finiteFreeOpen (fun x ↦ inferInstance)
    ∀ (J : D'.subscheme.IdealSheafData),
      let T := J.subscheme
      ∀
      (h_finitePresentation : Scheme.Hom.FinitePresentation J.subschemeι)
      (h_contains : J ≤ (((D'.subschemeι ≫ b) ⁻¹ᵁ Wₑ).ι).ker)
      (h_finiteLocallyFree : finiteLocallyFreeOn
        ((RingedSpace.modulePullbackDerived
          (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) ⊤)
      (h_rank : ∀ (i : ℤ) (t : T),
        (J.subschemeι ≫ D'.subschemeι ≫ b) t ∈ Wₑ →
          Module.rank (T.presheaf.stalk t)
              (cohomologyStalk ((RingedSpace.modulePullbackDerived
                (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) i t) =
            Module.rank (X.presheaf.stalk ((J.subschemeι ≫ D'.subschemeι ≫ b) t))
              (M.cohomologyStalk i ((J.subschemeι ≫ D'.subschemeι ≫ b) t))),
      let W := hM.rankProfileOpen ρ
      let S := (D'.subschemeι ≫ b) ⁻¹ᵁ W
      let Eₜ := (RingedSpace.modulePullbackDerived
        (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q
      ∃ U : T.Opens, IsClopen (U : Set T) ∧
        (∃ hS : J ≤ S.ι.ker, ∃ k : S.toScheme ⟶ U.toScheme,
          k ≫ U.ι = J.lift S.ι hS) ∧
        rankProfileOn Eₜ ρ U := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
