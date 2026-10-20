/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.Separation
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.ActionSeparation

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

/- Lemma 66.14.3 (1) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.quasiSeparated_hom_fppfQuotient :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
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
    [QuasiSeparated G.U.hom],
    QuasiSeparated M.hom)

/- Lemma 66.14.3 (2) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.quasiSeparatedSpace_fppfQuotient :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
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
    [QuasiSeparatedSpace G.U.left],
    QuasiSeparatedSpace M.left)

/- Lemma 66.14.3 (3) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.isSeparated_hom_fppfQuotient :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
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
    [IsSeparated G.U.hom],
    IsSeparated M.hom)

/- Lemma 66.14.3 (4) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.isSeparated_fppfQuotient :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
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
    [Scheme.IsSeparated G.U.left],
    Scheme.IsSeparated M.left)

/- Lemma 66.14.3 (5) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.quasiSeparated_hom_fppfQuotient_ofAction :
    ∀ {S : Scheme.{u}}
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
    [QuasiSeparated X.X.hom],
    QuasiSeparated M.hom)

/- Lemma 66.14.3 (6) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.quasiSeparatedSpace_fppfQuotient_ofAction :
    ∀ {S : Scheme.{u}}
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
    [QuasiSeparatedSpace X.X.left],
    QuasiSeparatedSpace M.left)

/- Lemma 66.14.3 (7) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.isSeparated_hom_fppfQuotient_ofAction :
    ∀ {S : Scheme.{u}}
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
    [IsSeparated X.X.hom],
    IsSeparated M.hom)

/- Lemma 66.14.3 (8) -/
@[stacks 0BBM] #check (AlgebraicGeometry.GroupoidScheme.isSeparated_fppfQuotient_ofAction :
    ∀ {S : Scheme.{u}}
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
    [Scheme.IsSeparated X.X.left],
    Scheme.IsSeparated M.left)

end AlgebraicGeometry.GroupoidScheme
