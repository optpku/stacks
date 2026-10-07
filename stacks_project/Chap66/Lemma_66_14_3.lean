module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import stacks_project.Chap66.Lemma_66_14_2
public import stacks_project.Chap66.Proposition_66_14_1

/-!
# Quasi-separated and separated finite locally free quotients

A scheme representing a finite locally free fppf groupoid quotient inherits
quasi-separatedness and separatedness from the object scheme, relatively over `S`
and absolutely. The same transfers hold for free finite locally free action
quotients.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 66.14.3 (1): under the hypotheses of Proposition 66.14.1, if `G.U` is
quasi-separated over `S`, then any scheme `M` representing the fppf quotient `U / R`
is quasi-separated over `S`. -/
@[stacks 0BBM]
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

/-- Lemma 66.14.3 (2): under the hypotheses of Proposition 66.14.1, if `G.U` is
quasi-separated, then any scheme `M` representing the fppf quotient `U / R` is
quasi-separated. -/
@[stacks 0BBM]
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

/-- Lemma 66.14.3 (3): under the hypotheses of Proposition 66.14.1, if `G.U` is
separated over `S`, then any scheme `M` representing the fppf quotient `U / R` is
separated over `S`. -/
@[stacks 0BBM]
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

/-- Lemma 66.14.3 (4): under the hypotheses of Proposition 66.14.1, if `G.U` is
separated, then any scheme `M` representing the fppf quotient `U / R` is
separated. -/
@[stacks 0BBM]
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

/-- Lemma 66.14.3 (5): under the hypotheses of Lemma 66.14.2, if `X` is quasi-separated
over `S`, then any scheme `M` representing the fppf quotient `X / G` is
quasi-separated over `S`. -/
@[stacks 0BBM]
theorem quasiSeparated_hom_fppfQuotient_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (hcond : hasAffineOrbitSourceCondition G X)
    {M : Over S} (q : (ofAction G X).U ⟶ M)
    (h_eq : (ofAction G X).toPreRelation.t ≫ q =
      (ofAction G X).toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso ((ofAction G X).toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _
      (ofAction G X).toPreRelation (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [QuasiSeparated X.X.hom] :
    QuasiSeparated M.hom := sorry

/-- Lemma 66.14.3 (6): under the hypotheses of Lemma 66.14.2, if `X` is
quasi-separated, then any scheme `M` representing the fppf quotient `X / G` is
quasi-separated. -/
@[stacks 0BBM]
theorem quasiSeparatedSpace_fppfQuotient_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (hcond : hasAffineOrbitSourceCondition G X)
    {M : Over S} (q : (ofAction G X).U ⟶ M)
    (h_eq : (ofAction G X).toPreRelation.t ≫ q =
      (ofAction G X).toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso ((ofAction G X).toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _
      (ofAction G X).toPreRelation (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [QuasiSeparatedSpace X.X.left] :
    QuasiSeparatedSpace M.left := sorry

/-- Lemma 66.14.3 (7): under the hypotheses of Lemma 66.14.2, if `X` is separated
over `S`, then any scheme `M` representing the fppf quotient `X / G` is
separated over `S`. -/
@[stacks 0BBM]
theorem isSeparated_hom_fppfQuotient_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (hcond : hasAffineOrbitSourceCondition G X)
    {M : Over S} (q : (ofAction G X).U ⟶ M)
    (h_eq : (ofAction G X).toPreRelation.t ≫ q =
      (ofAction G X).toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso ((ofAction G X).toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _
      (ofAction G X).toPreRelation (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [IsSeparated X.X.hom] :
    IsSeparated M.hom := sorry

/-- Lemma 66.14.3 (8): under the hypotheses of Lemma 66.14.2, if `X` is separated,
then any scheme `M` representing the fppf quotient `X / G` is separated. -/
@[stacks 0BBM]
theorem isSeparated_fppfQuotient_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (hcond : hasAffineOrbitSourceCondition G X)
    {M : Over S} (q : (ofAction G X).U ⟶ M)
    (h_eq : (ofAction G X).toPreRelation.t ≫ q =
      (ofAction G X).toPreRelation.s ≫ q)
    (hq : IsFiniteLocallyFree q.left)
    (hker : IsIso ((ofAction G X).toPreRelation.kernelPairLift q h_eq))
    (hquot : IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _
      (ofAction G X).toPreRelation (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      q h_eq))
    [Scheme.IsSeparated X.X.left] :
    Scheme.IsSeparated M.left := sorry

end AlgebraicGeometry.GroupoidScheme
