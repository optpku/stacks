module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Reconstruction
import StacksCheckRecall

/-!
# Recovering isomorphisms of algebraic spaces over Spec ℤ from ringed topoi

If a morphism of small étale ringed topoi between algebraic spaces over `Spec ℤ`
is a ringed equivalence, then it is `2`-isomorphic to the morphism of ringed topoi
induced by a unique morphism of algebraic spaces, and that morphism is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Lemma 66.28.5: Each structure-map component of a ringed-topos equivalence is local. -/
@[stacks 05YZ] #check
  (AlgebraicGeometry.AlgebraicSpace.toposHomStructureMapApp_isLocalHom_of_isEquivalence :
    ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
      (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
      [g.IsEquivalence] (U : (smallEtaleSite X)ᵒᵖ),
      IsLocalHom (toposHomStructureMapApp g U))

/- Lemma 66.28.5 (1): An equivalence of small étale ringed topoi is induced, up to
`2`-isomorphism, by a unique morphism of algebraic spaces over `Spec ℤ`. -/
@[stacks 05YZ] #check
  (AlgebraicGeometry.AlgebraicSpace.existsUnique_algebraicSpaceHom_of_smallEtale_ringedTopos_isEquivalence :
    ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
      (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y)) [g.IsEquivalence],
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
          g (ringedToposHom f)))

/- Lemma 66.28.5 (2): A morphism inducing a small étale ringed-topos morphism
`2`-isomorphic to a ringed-topos equivalence is an isomorphism of algebraic spaces. -/
@[stacks 05YZ] #check
  (AlgebraicGeometry.AlgebraicSpace.isIso_of_smallEtale_ringedTopos_twoIso :
    ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
      (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y))
      [g.IsEquivalence] {f : X ⟶ Y}
      [Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
        g (ringedToposHom f))],
      IsIso f)
