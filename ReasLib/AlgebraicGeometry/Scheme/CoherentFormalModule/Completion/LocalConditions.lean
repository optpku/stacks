module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module over a local Noetherian ring with a dualizing complex and
cohomological dimension one satisfies the `(2, 3)`-inequalities if its completed stalks
are finite locally free away from the completed ideal and either the localizations
outside `V(I)` satisfy `(S₂)` with component dimension at least four, or the primewise
depth-plus-quotient-dimension bound outside `V(I)` holds. -/
theorem satisfiesInequalities_of_local_conditions
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_finiteLocallyFree :
      ∀ y : S.Y, (hy : S.y y ∈ S.U) →
        ∀ g : completedLocalRing S (closedFiberOpenPoint S y hy),
          g ∈ completedIdeal S (closedFiberOpenPoint S y hy) →
            Module.FiniteLocallyFree (Localization.Away g)
              (LocalizedModule.Away g
                (completedStalk S F (closedFiberOpenPoint S y hy))))
    (h_alternative :
      ((∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (S.I : Set A) →
          SerreConditionS (Localization.AtPrime p.asIdeal) 2) ∧
        (∀ Z : irreducibleComponents S.X,
          ¬ ((Z : Set S.X) ⊆ Set.range S.y) →
            (4 : WithBot ℕ∞) ≤ topologicalKrullDim Z)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (S.I : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (S.I : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal)))) :
    SatisfiesInequalities S F 2 3 := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
