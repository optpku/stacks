/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import stacks_project.Chap59.Lemma_59_40_3
public import stacks_project.Chap59.Lemma_59_40_4

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/-- Theorem 59.40.5 (1): for schemes `X` and `Y`, every morphism of locally ringed topoi from the
small étale ringed topos of `X` to that of `Y` is uniquely 2-isomorphic to
`(Etale.Small.liftedRingedHom f).toToposHom` for a unique scheme morphism `f : X ⟶ Y`. -/
@[stacks 04I7]
theorem existsUnique_schemeHom_of_smallEtale_locallyRingedTopos_ofScheme
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
        g (Etale.Small.liftedRingedHom f).toToposHom) := sorry

/-- Induced small étale topos morphisms are 2-isomorphic if and only if the scheme morphisms
coincide. -/
theorem smallEtale_inducedToposHom_twoIso_iff_eq {X Y : Scheme.{u}} {a b : X ⟶ Y} :
    Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      (Etale.Small.liftedRingedHom a).toToposHom
      (Etale.Small.liftedRingedHom b).toToposHom) ↔ a = b := sorry

/-- Theorem 59.40.5 (2): the assignment sending a scheme to its small étale locally ringed topos
is fully faithful with morphisms on the right taken up to 2-isomorphisms: a morphism of ringed
topoi is locally ringed if and only if it is uniquely 2-isomorphic to
`(Etale.Small.liftedRingedHom f).toToposHom` for a unique scheme morphism `f : X ⟶ Y`. -/
@[stacks 04I7]
theorem smallEtaleLocallyRingedTopos_fullyFaithful {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y)) :
    (∀ U, IsLocalHom (toposHomStructureMapApp g U)) ↔
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
          g (Etale.Small.liftedRingedHom f).toToposHom) := sorry

end Hom
end Scheme
end AlgebraicGeometry
