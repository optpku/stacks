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
cohomological dimension one satisfies the `(2, 3)`-inequalities if `I` and `(f)` have
equal radicals, its completed stalks are finite locally free away from the completed
ideal, and either `A_f` satisfies `(S₂)` with dimension at least four for components
not contained in `V(I)`, or the primewise depth-plus-quotient-dimension bound outside
`V(f)` holds. -/
theorem satisfiesInequalities_of_local_conditions
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (f : A)
    -- Source context: f is not introduced in the Stacks statement; Lemma lemma-equivalence-better applies it with I = (f), and the proof needs V(f) = V(I).
    (h_I_radical : S.I.radical = (Ideal.span ({f} : Set A)).radical)
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
      (SerreConditionS (Localization.Away f) 2 ∧
        (∀ Z : irreducibleComponents S.X,
          ¬ ((Z : Set S.X) ⊆ Set.range S.y) →
            (4 : WithBot ℕ∞) ≤ topologicalKrullDim Z)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ({f} : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus ({f} : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal)))) :
    SatisfiesInequalities S F 2 3 := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
