module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Reconstruction
import StacksCheckRecall

/-!
# Recovering morphisms of algebraic spaces over Spec ℤ from locally ringed topoi

Every morphism of locally ringed small étale topoi between algebraic spaces over `Spec ℤ`
is `2`-isomorphic to the morphism of ringed topoi induced by a unique morphism of
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Theorem 66.28.4: Every locally ringed morphism of small étale topoi of algebraic spaces
over `Spec ℤ` is `2`-isomorphic to the morphism induced by a unique algebraic-space morphism. -/
@[stacks 04KL] #check
  (AlgebraicGeometry.AlgebraicSpace.existsUnique_algebraicSpaceHom_of_smallEtale_locallyRingedTopos :
    ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
      (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y)),
      (∀ U, IsLocalHom (toposHomStructureMapApp g U)) →
        ExistsUnique fun f : X ⟶ Y ↦
          Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
            g (ringedToposHom f)))

#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleLocallyRingedTopos_fullyFaithful :
  ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (g : RingedSite.ToposHom (ringedSite X) (ringedSite Y)),
    (∀ U, IsLocalHom (toposHomStructureMapApp g U)) ↔
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
          g (ringedToposHom f)))
