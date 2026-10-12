/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Recovering morphisms of algebraic spaces over Spec ℤ from locally ringed topoi

Every morphism of locally ringed small étale topoi between algebraic spaces over `Spec ℤ`
is uniquely `2`-isomorphic to the morphism of ringed topoi induced by a unique morphism of
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Component of the inverse-image structure-sheaf map of a morphism of small étale ringed
topoi of algebraic spaces over `Spec ℤ`. -/
def toposHomStructureMapApp
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    (U : (smallEtaleSite X)ᵒᵖ) :=
  (g.structureMap.hom.app U).hom

/-- Objectwise locality of a morphism of small étale ringed topoi is locality of each
structure-sheaf component. -/
theorem toposHomStructureMapApp_isLocalHom
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) (U) :
    IsLocalHom (toposHomStructureMapApp g U) :=
  sorry

/-- Theorem 66.28.4: let `X`, `Y` be algebraic spaces over `Spec ℤ`. Every morphism of
locally ringed topoi `(g, g.structureMap) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` is
uniquely `2`-isomorphic to `ringedToposHom f` for a unique morphism of algebraic spaces
`f : X ⟶ Y`. Locally ringed means objectwise `IsLocalHom` of the components of
`g.structureMap`. The construction `X ↦ (X_étale, 𝒪_X)` is fully faithful, with morphisms
on the right taken up to `2`-isomorphisms. -/
@[stacks 04KL]
theorem existsUnique_algebraicSpaceHom_of_smallEtale_locallyRingedTopos
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
        g (ringedToposHom f)) :=
  sorry

/-- The assignment sending an algebraic space over `Spec ℤ` to its small étale locally ringed
topos is fully faithful with morphisms on the right taken up to `2`-isomorphisms: a morphism of
ringed topoi is locally ringed if and only if it is uniquely `2`-isomorphic to
`ringedToposHom f` for a unique morphism of algebraic spaces `f : X ⟶ Y`. -/
theorem smallEtaleLocallyRingedTopos_fullyFaithful
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y)) :
    (∀ U, IsLocalHom (toposHomStructureMapApp g U)) ↔
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
          g (ringedToposHom f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
