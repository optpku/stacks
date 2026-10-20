/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Reconstruction of algebraic-space morphisms from small étale ringed topoi

An objectwise-local morphism of small étale ringed topoi of algebraic spaces over `Spec ℤ`
is `2`-isomorphic to the morphism induced by a unique morphism of algebraic spaces.
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

/-- Every objectwise-local morphism of small étale ringed topoi of algebraic spaces over
`Spec ℤ` is `2`-isomorphic to the morphism induced by a unique morphism of algebraic spaces. -/
theorem existsUnique_algebraicSpaceHom_of_smallEtale_locallyRingedTopos
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
        g (ringedToposHom f)) :=
  sorry

/-- A morphism of small étale ringed topoi of algebraic spaces over `Spec ℤ` is objectwise
local if and only if it is `2`-isomorphic to the morphism induced by a unique morphism of
algebraic spaces. -/
theorem smallEtaleLocallyRingedTopos_fullyFaithful
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y)) :
    (∀ U, IsLocalHom (toposHomStructureMapApp g U)) ↔
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
          g (ringedToposHom f)) := by
  constructor
  · exact existsUnique_algebraicSpaceHom_of_smallEtale_locallyRingedTopos g
  · intro h
    sorry

/-- Each component of the inverse-image structure-sheaf map of an equivalence of small
étale ringed topoi of algebraic spaces over `Spec ℤ` is a local ring homomorphism. -/
theorem toposHomStructureMapApp_isLocalHom_of_isEquivalence
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    [g.IsEquivalence] (U : (smallEtaleSite X)ᵒᵖ) :
    IsLocalHom (toposHomStructureMapApp g U) :=
  sorry

/-- Every equivalence of small étale ringed topoi of algebraic spaces over `Spec ℤ` is
`2`-isomorphic to the morphism induced by a unique morphism of algebraic spaces. -/
theorem existsUnique_algebraicSpaceHom_of_smallEtale_ringedTopos_isEquivalence
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    [g.IsEquivalence] :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
        g (ringedToposHom f)) :=
  sorry

/-- A morphism of algebraic spaces over `Spec ℤ` whose induced small étale ringed-topos
morphism is `2`-isomorphic to a ringed-topos equivalence is an isomorphism. -/
theorem isIso_of_smallEtale_ringedTopos_twoIso
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    [g.IsEquivalence] {f : X ⟶ Y}
    [Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      g (ringedToposHom f))] :
    IsIso f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
