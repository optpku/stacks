/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import stacks_project.Chap66.Theorem_66_28_4

/-!
# Recovering isomorphisms of algebraic spaces over Spec ℤ from ringed topoi

If a morphism of small étale ringed topoi between algebraic spaces over `Spec ℤ`
is a ringed equivalence, then it is uniquely `2`-isomorphic to the morphism of
ringed topoi induced by a unique isomorphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Objectwise locality of an equivalence of small étale ringed topoi of algebraic
spaces over `Spec ℤ`: each component of `g.structureMap` is a local ring
homomorphism. -/
instance toposHomStructureMapApp_isLocalHom_of_isEquivalence
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    [g.IsEquivalence] (U) :
    IsLocalHom (toposHomStructureMapApp g U) :=
  sorry

/-- Lemma 66.28.5 (1): let `X`, `Y` be algebraic spaces over `Spec ℤ`. If
`(g, g.structureMap) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` is an
isomorphism of ringed topoi, then there exists a unique morphism `f : X ⟶ Y`
of algebraic spaces such that `(g, g.structureMap)` is `2`-isomorphic to
`ringedToposHom f`. -/
@[stacks 05YZ]
theorem existsUnique_algebraicSpaceHom_of_smallEtale_ringedTopos_isEquivalence
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    [g.IsEquivalence] :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
        g (ringedToposHom f)) :=
  sorry

/-- Lemma 66.28.5 (2): let `X`, `Y` be algebraic spaces over `Spec ℤ`. If
`(g, g.structureMap)` is an isomorphism of ringed topoi and `f : X ⟶ Y` is a
morphism of algebraic spaces such that `(g, g.structureMap)` is `2`-isomorphic
to `ringedToposHom f`, then `f` is an isomorphism of algebraic spaces. -/
@[stacks 05YZ]
theorem isIso_of_smallEtale_ringedTopos_twoIso
    {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
    [g.IsEquivalence] {f : X ⟶ Y}
    [Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      g (ringedToposHom f))] :
    IsIso f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
