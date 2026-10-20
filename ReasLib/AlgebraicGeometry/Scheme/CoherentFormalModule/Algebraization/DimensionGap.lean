module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.RingTheory.Flatness.LocallyFree
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module extends across the closed complement when the ambient
ring is local with an intrinsic dualizing complex, the geometry is equidimensional
and Cohen–Macaulay off the smaller closed subset, and the dimension-gap and
completed-stalk hypotheses hold. -/
theorem extendsTo_of_dimensionGap
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
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
            (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))) :
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F := sorry

/-- Under the same dimension-gap hypotheses, adic completeness identifies the
coherent formal module with the completion of a coherent module on the open
complement. -/
theorem isCompletion_of_dimensionGap
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
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
            (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
