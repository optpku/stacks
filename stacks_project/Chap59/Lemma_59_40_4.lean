/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small.Reconstruction
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory RingedSite

/- Lemma 59.40.4 -/
@[stacks 04I6] #check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_schemeHom_of_smallEtale_locallyRingedTopos :
    ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
      (g : ToposHom (Scheme.Etale.Small.liftedRingedSite X)
        (Scheme.Etale.Small.liftedRingedSite Y)),
      (∀ U, IsLocalHom (Scheme.Hom.toposHomStructureMapApp g U)) →
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
          g (Scheme.Etale.Small.liftedRingedHom f).toToposHom))
