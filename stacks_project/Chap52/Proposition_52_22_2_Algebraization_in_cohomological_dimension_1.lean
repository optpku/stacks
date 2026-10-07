module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.CohomologicalDimensionOne
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Proposition 52.22.2 (Algebraization in cohomological dimension 1) (1): in
Situation 52.16.1, a coherent formal module satisfying the `(2, 3)`-inequalities
extends to `S.X` when `A` has a dualizing complex and
`Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1`. -/
@[stacks 0EJJ] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.extends_of_cohomologicalDimension_one :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (h_dualizing :
        ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
      (h_cd :
        Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_ineq : SatisfiesInequalities S F 2 3),
      extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F)

/- Proposition 52.22.2 (Algebraization in cohomological dimension 1) (2): if
`A` is `S.I`-adically complete under the hypotheses of (1), then the coherent
formal module is the completion of a coherent `𝒪_{S.U}`-module. -/
@[stacks 0EJJ] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_cohomologicalDimension_one :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
      (h_dualizing :
        ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
      (h_cd :
        Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_ineq : SatisfiesInequalities S F 2 3),
      (Scheme.CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
