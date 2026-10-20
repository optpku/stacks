/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small.RingedTopos

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/-- The component of the structure-sheaf map of a morphism of small étale ringed topoi. -/
def toposHomStructureMapApp
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (U) :=
  let φ := g.structureMap
  let ψ := φ.hom
  (ψ.app U).hom

/-- Two scheme morphisms inducing 2-isomorphic small étale ringed-topos morphisms to the
same ringed-topos morphism are equal. -/
theorem unique_schemeHom_of_smallEtale_twoIso
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    {f₁ f₂ : X ⟶ Y}
    (h₁ : Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      g (Etale.Small.liftedRingedHom f₁).toToposHom))
    (h₂ : Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      g (Etale.Small.liftedRingedHom f₂).toToposHom)) :
    f₁ = f₂ := sorry

/-- For affine schemes, an objectwise-local morphism of their small étale ringed topoi
is 2-isomorphic to the morphism induced by a unique scheme morphism. -/
theorem existsUnique_schemeHom_of_smallEtale_locallyRingedTopos
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
        g (Etale.Small.liftedRingedHom f).toToposHom) := sorry

/-- For arbitrary schemes, an objectwise-local morphism of their small étale ringed topoi
is 2-isomorphic to the morphism induced by a unique scheme morphism. -/
theorem existsUnique_schemeHom_of_smallEtale_locallyRingedTopos_ofScheme
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
        g (Etale.Small.liftedRingedHom f).toToposHom) := sorry

/-- Induced small étale ringed-topos morphisms are 2-isomorphic if and only if the scheme
morphisms coincide. -/
theorem smallEtale_inducedToposHom_twoIso_iff_eq {X Y : Scheme.{u}} {a b : X ⟶ Y} :
    Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      (Etale.Small.liftedRingedHom a).toToposHom
      (Etale.Small.liftedRingedHom b).toToposHom) ↔ a = b := sorry

/-- A morphism between the small étale ringed topoi of schemes is objectwise local if and
only if it is 2-isomorphic to the morphism induced by a unique scheme morphism. -/
theorem smallEtaleLocallyRingedTopos_fullyFaithful {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y)) :
    (∀ U, IsLocalHom (toposHomStructureMapApp g U)) ↔
      ExistsUnique fun f : X ⟶ Y ↦
        Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
          g (Etale.Small.liftedRingedHom f).toToposHom) := sorry

end Hom
end Scheme
end AlgebraicGeometry
