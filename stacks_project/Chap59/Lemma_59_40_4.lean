module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import stacks_project.Chap59.Lemma_59_40_3

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/-- Component of the structure-sheaf map of a morphism of ringed topoi. -/
def toposHomStructureMapApp
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (U) :=
  let φ := g.structureMap
  let ψ := φ.hom
  (ψ.app U).hom

/-- Locality of structure-sheaf components of a morphism of ringed topoi. -/
theorem toposHomStructureMapApp_isLocalHom
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) (U) :
    IsLocalHom (toposHomStructureMapApp g U) := sorry

/-- Lemma 59.40.4: if `X` and `Y` are affine schemes and `g` is a morphism of locally ringed
topoi from the small étale ringed topos of `X` to that of `Y`, then there is a unique scheme
morphism `f : X ⟶ Y` such that `g` is 2-isomorphic to
`(Etale.Small.liftedRingedHom f).toToposHom` in the sense of Modules on Sites,
Definition 18.8.1 (`ToposHom.TwoIso`). -/
@[stacks 04I6]
theorem existsUnique_schemeHom_of_smallEtale_locallyRingedTopos
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    (h_local : ∀ U, IsLocalHom (toposHomStructureMapApp g U)) :
    ExistsUnique fun f : X ⟶ Y ↦
      Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
        g (Etale.Small.liftedRingedHom f).toToposHom) := sorry

/-- Uniqueness of a scheme morphism whose small étale ringed-topos morphism is 2-isomorphic to a
fixed morphism of ringed topoi, recovered from Lemma 59.40.3. -/
theorem unique_schemeHom_of_smallEtale_twoIso
    {X Y : Scheme.{u}}
    (g : ToposHom (Etale.Small.liftedRingedSite X) (Etale.Small.liftedRingedSite Y))
    {f₁ f₂ : X ⟶ Y}
    (h₁ : Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      g (Etale.Small.liftedRingedHom f₁).toToposHom))
    (h₂ : Nonempty (ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      g (Etale.Small.liftedRingedHom f₂).toToposHom)) :
    f₁ = f₂ := sorry

end Hom
end Scheme
end AlgebraicGeometry
