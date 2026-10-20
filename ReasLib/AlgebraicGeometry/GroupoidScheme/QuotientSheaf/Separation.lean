module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.FiniteLocallyFree

/-!
# Separation properties of finite locally free groupoid quotients

Represented finite locally free groupoid quotients inherit quasi-separatedness
and separatedness from their object schemes, over the base and absolutely.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A scheme representing a finite locally free groupoid quotient is quasi-separated
over the base when the object scheme is quasi-separated over the base. -/
theorem quasiSeparated_hom_fppfQuotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] [HasAffineOrbitClosedPoint G]
    {M : Over S} (q : G.U ⟶ M)
    (h_eq : G.toPreRelation.t ≫ q = G.toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso (G.toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
      (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [QuasiSeparated G.U.hom] :
    QuasiSeparated M.hom := sorry

/-- A scheme representing a finite locally free groupoid quotient is quasi-separated
when the object scheme is quasi-separated. -/
theorem quasiSeparatedSpace_fppfQuotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] [HasAffineOrbitClosedPoint G]
    {M : Over S} (q : G.U ⟶ M)
    (h_eq : G.toPreRelation.t ≫ q = G.toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso (G.toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
      (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [QuasiSeparatedSpace G.U.left] :
    QuasiSeparatedSpace M.left := sorry

/-- A scheme representing a finite locally free groupoid quotient is separated
over the base when the object scheme is separated over the base. -/
theorem isSeparated_hom_fppfQuotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] [HasAffineOrbitClosedPoint G]
    {M : Over S} (q : G.U ⟶ M)
    (h_eq : G.toPreRelation.t ≫ q = G.toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso (G.toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
      (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [IsSeparated G.U.hom] :
    IsSeparated M.hom := sorry

/-- A scheme representing a finite locally free groupoid quotient is separated
when the object scheme is separated. -/
theorem isSeparated_fppfQuotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] [HasAffineOrbitClosedPoint G]
    {M : Over S} (q : G.U ⟶ M)
    (h_eq : G.toPreRelation.t ≫ q = G.toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso (G.toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
      (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [Scheme.IsSeparated G.U.left] :
    Scheme.IsSeparated M.left := sorry

end AlgebraicGeometry.GroupoidScheme
