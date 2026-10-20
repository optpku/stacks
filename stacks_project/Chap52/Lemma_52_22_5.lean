/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Situation_52_16_1
public import stacks_project.Chap52.Definition_52_16_5
public import stacks_project.Chap52.Lemma_52_16_11
public import stacks_project.Chap52.Lemma_52_16_3_Instances
public import stacks_project.Chap52.Definition_52_19_1_Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.DimensionGap
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.LocallyFreeStalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.22.5 (1): under Situation 52.16.1, local dualizing,
equidimensional, Cohen-Macaulay, dimension-gap, generation, and completed-stalk
hypotheses, the coherent formal module extends to `S.X`. -/
@[stacks 0EJP] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.extendsTo_of_dimensionGap :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A)
    [EquidimensionalSpace S.X]
    [Scheme.CohenMacaulay
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).openComplement.toScheme)]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (f : Fin d → A)
    (h_generate : S.I = Ideal.span (Set.range f))
    (h_dim : topologicalKrullDim S.Z + ((d + 2 : ℕ) : WithBot ℕ∞) <
      topologicalKrullDim S.X)
    (h_stalk : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      ∀ p : PrimeSpectrum (completedLocalRing S yU),
        p ∉ PrimeSpectrum.zeroLocus
            (completedIdeal S yU : Set (completedLocalRing S yU)) →
          Module.FiniteLocallyFree (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))),
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F)

/- Lemma 52.22.5 (2): under the same hypotheses as (1), if `A` is `S.I`-adically
complete, then the coherent formal module is the completion of a coherent module. -/
@[stacks 0EJP] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_dimensionGap :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
    [EquidimensionalSpace S.X]
    [Scheme.CohenMacaulay
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).openComplement.toScheme)]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (f : Fin d → A)
    (h_generate : S.I = Ideal.span (Set.range f))
    (h_dim : topologicalKrullDim S.Z + ((d + 2 : ℕ) : WithBot ℕ∞) <
      topologicalKrullDim S.X)
    (h_stalk : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      ∀ p : PrimeSpectrum (completedLocalRing S yU),
        p ∉ PrimeSpectrum.zeroLocus
            (completedIdeal S yU : Set (completedLocalRing S yU)) →
          Module.FiniteLocallyFree (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))),
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

/- Lemma 52.22.5 (3): finite local freeness of every stage implies finite local
freeness of each completed stalk away from the vanishing locus of the completed ideal. -/
@[stacks 0EJP] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.finiteLocallyFreeOutside_of_finiteLocallyFreeStages :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n),
    ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      ∀ p : PrimeSpectrum (completedLocalRing S yU),
        p ∉ PrimeSpectrum.zeroLocus
            (completedIdeal S yU : Set (completedLocalRing S yU)) →
          Module.FiniteLocallyFree (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU)))

end AlgebraicGeometry.Scheme.CoherentFormalModules
