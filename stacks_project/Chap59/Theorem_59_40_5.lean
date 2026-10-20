module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small.Reconstruction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/- Theorem 59.40.5 (1): every locally ringed morphism between the small étale topoi of
schemes is induced, up to compatible 2-isomorphism, by a unique scheme morphism. -/
@[stacks 04I7] #check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_schemeHom_of_smallEtale_locallyRingedTopos_ofScheme :
    ∀ {X Y : Scheme.{u}}
      (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y)),
      (∀ U, IsLocalHom (toposHomStructureMapApp g U)) →
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
          g (Etale.Small.liftedRingedHom f).toToposHom))

/- Induced small étale topos morphisms are 2-isomorphic if and only if the scheme morphisms
coincide. -/
#check
  (AlgebraicGeometry.Scheme.Hom.smallEtale_inducedToposHom_twoIso_iff_eq :
    ∀ {X Y : Scheme.{u}} {a b : X ⟶ Y},
      Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
        (Etale.Small.liftedRingedHom a).toToposHom
        (Etale.Small.liftedRingedHom b).toToposHom) ↔ a = b)

/- Theorem 59.40.5 (2): the assignment sending a scheme to its small étale locally ringed topos
is fully faithful with morphisms on the right taken up to 2-isomorphisms: a morphism of ringed
topoi is locally ringed if and only if it is uniquely 2-isomorphic to
`(Etale.Small.liftedRingedHom f).toToposHom` for a unique scheme morphism `f : X ⟶ Y`. -/
@[stacks 04I7] #check
  (AlgebraicGeometry.Scheme.Hom.smallEtaleLocallyRingedTopos_fullyFaithful :
    ∀ {X Y : Scheme.{u}}
      (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y)),
      (∀ U, IsLocalHom (toposHomStructureMapApp g U)) ↔
        ExistsUnique fun f : X ⟶ Y ↦
          Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
            g (Etale.Small.liftedRingedHom f).toToposHom))

end Hom
end Scheme
end AlgebraicGeometry
