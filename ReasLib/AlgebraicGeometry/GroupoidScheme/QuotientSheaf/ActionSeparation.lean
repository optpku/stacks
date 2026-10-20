module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.Separation
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.ActionFiniteLocallyFree

/-!
# Separation properties of free finite locally free action quotients

Represented quotients of free finite locally free actions satisfying the
affine-orbit source condition inherit quasi-separatedness and separatedness
from the action schemes, over the base and absolutely.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A scheme representing the fppf quotient of a free finite locally free action
satisfying the affine-orbit source condition is quasi-separated over the base
when the action scheme is quasi-separated over the base. -/
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

/-- A scheme representing the fppf quotient of a free finite locally free action
satisfying the affine-orbit source condition is quasi-separated
when the action scheme is quasi-separated. -/
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

/-- A scheme representing the fppf quotient of a free finite locally free action
satisfying the affine-orbit source condition is separated over the base
when the action scheme is separated over the base. -/
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

/-- A scheme representing the fppf quotient of a free finite locally free action
satisfying the affine-orbit source condition is separated
when the action scheme is separated. -/
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
