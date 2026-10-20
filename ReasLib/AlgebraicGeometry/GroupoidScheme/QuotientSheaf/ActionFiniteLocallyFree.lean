/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Radicial
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical
public import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction

/-!
# Free finite locally free action quotients

A free action of a finite locally free group scheme has representable fppf quotient,
which is an fppf torsor, under geometric alternatives on the structure morphism,
open embeddings of the object scheme, or radiciality of the group scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The structure morphism is affine, quasi-affine, projective, or quasi-projective,
the object scheme admits an open immersion into an affine scheme or into `Proj 𝒜`,
or the group scheme is radicial. -/
def hasAffineOrbitSourceCondition {S : Scheme.{u}} (G : Grp (Over S))
    (X : GroupScheme.Action G) : Prop :=
  IsAffineHom X.X.hom ∨
    QuasiAffineHom X.X.hom ∨
    Projective X.X.hom ∨
    QuasiProjective X.X.hom ∨
    (∃ (Y : Scheme.{u}) (i : X.X.left ⟶ Y), IsAffine Y ∧ IsOpenImmersion i) ∨
    (∃ (A : Type u) (σ : Type u) (_ : CommRing A) (_ : SetLike σ A)
      (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
      (i : X.X.left ⟶ Proj 𝒜), IsOpenImmersion i) ∨
    Radicial G.X.hom

/-- The affine-orbit condition is equivalent to its seven geometric alternatives. -/
theorem hasAffineOrbitSourceCondition_iff {S : Scheme.{u}} (G : Grp (Over S))
    (X : GroupScheme.Action G) :
    hasAffineOrbitSourceCondition G X ↔
      IsAffineHom X.X.hom ∨
        QuasiAffineHom X.X.hom ∨
        Projective X.X.hom ∨
        QuasiProjective X.X.hom ∨
        (∃ (Y : Scheme.{u}) (i : X.X.left ⟶ Y), IsAffine Y ∧ IsOpenImmersion i) ∨
        (∃ (A : Type u) (σ : Type u) (_ : CommRing A) (_ : SetLike σ A)
          (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
          (i : X.X.left ⟶ Proj 𝒜), IsOpenImmersion i) ∨
        Radicial G.X.hom := sorry

/-- A free action of a group scheme yields an equivalence relation on the action groupoid. -/
instance instIsEquivalenceRelation_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G) [Mod.IsFree X] :
    IsEquivalenceRelation (ofAction G X).t (ofAction G X).s := sorry

/-- Finite local freeness of `G → S` implies finite local freeness of the action-groupoid
source. -/
instance instIsFiniteLocallyFree_ofAction_s {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G) [IsFiniteLocallyFree G.X.hom] :
    IsFiniteLocallyFree (ofAction G X).s.left := sorry

/-- Finite local freeness of `G → S` implies finite local freeness of the action-groupoid
target. -/
instance instIsFiniteLocallyFree_ofAction_t {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G) [IsFiniteLocallyFree G.X.hom] :
    IsFiniteLocallyFree (ofAction G X).t.left := sorry

/-- For a free finite locally free action, the seven geometric alternatives imply that
every nonempty closed subset meets an orbit contained in an affine open. -/
theorem hasAffineOrbitClosedPoint_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (h : hasAffineOrbitSourceCondition G X) :
    HasAffineOrbitClosedPoint (ofAction G X) := sorry

/-- The fppf quotient of a free finite locally free action is representable under the
seven geometric alternatives. -/
theorem hasRepresentableQuotient_ofAction_fppf {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (h : hasAffineOrbitSourceCondition G X) :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- An affine structure morphism yields a representable fppf quotient of a free finite
locally free action. -/
instance instHasRepresentableQuotient_ofAction_isAffineHom {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X] [IsAffineHom X.X.hom] :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- A projective structure morphism yields a representable fppf quotient of a free finite
locally free action. -/
instance instHasRepresentableQuotient_ofAction_projective {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X] [Projective X.X.hom] :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- A quasi-projective structure morphism yields a representable fppf quotient of a free
finite locally free action. -/
instance instHasRepresentableQuotient_ofAction_quasiProjective {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X] [QuasiProjective X.X.hom] :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- A radicial finite locally free group scheme yields a representable fppf quotient of a
free action. -/
instance instHasRepresentableQuotient_ofAction_radicial {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X] [Radicial G.X.hom] :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- A quasi-affine structure morphism yields a representable fppf quotient of a free finite
locally free action. -/
theorem hasRepresentableQuotient_ofAction_of_quasiAffineHom {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (h : QuasiAffineHom X.X.hom) :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- An open immersion into an affine scheme yields a representable fppf quotient of a free
finite locally free action. -/
theorem hasRepresentableQuotient_ofAction_of_openImmersion_isAffine {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    {Y : Scheme.{u}} (i : X.X.left ⟶ Y) [IsAffine Y] [IsOpenImmersion i] :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- An open immersion into `Proj 𝒜` yields a representable fppf quotient of a free finite
locally free action. -/
theorem hasRepresentableQuotient_ofAction_of_openImmersion_proj {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (i : X.X.left ⟶ Proj 𝒜) [IsOpenImmersion i] :
    HasRepresentableQuotient StandardTopology.fppf (ofAction G X) := sorry

/-- A free finite locally free action satisfying the seven geometric alternatives admits
a scheme quotient with a finite locally free quotient map, a kernel-pair identification,
an identification of its fppf quotient sheaf, and fppf local surjectivity. -/
theorem exists_fppfTorsor_ofAction {S : Scheme.{u}}
    (G : Grp (Over S)) (X : GroupScheme.Action G)
    [IsFiniteLocallyFree G.X.hom] [Mod.IsFree X]
    (h : hasAffineOrbitSourceCondition G X) :
    ∃ (M : Over S) (q : X.X ⟶ M)
      (h_eq : (ofAction G X).toPreRelation.t ≫ q =
        (ofAction G X).toPreRelation.s ≫ q),
      IsFiniteLocallyFree q.left ∧
        IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _
          (ofAction G X).toPreRelation (StandardTopology.fppf.overTopology S)
          (StandardTopology.overTopologySubcanonical StandardTopology.fppf S) q h_eq) ∧
          IsIso ((ofAction G X).toPreRelation.kernelPairLift q h_eq) ∧
            Sheaf.IsLocallySurjective
              ((@GrothendieckTopology.uliftYoneda.{u + 1} (Over S) _
                  (StandardTopology.fppf.overTopology S)
                  (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)).map q) := sorry

end AlgebraicGeometry.GroupoidScheme
