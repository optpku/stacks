module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Etale
namespace Small

/-- The morphism of universe-lifted small étale ringed sites induced by a scheme morphism. -/
noncomputable def liftedRingedHom {S T : Scheme.{u}} (f : T ⟶ S) :
    RingedSite.Hom (liftedRingedSite T) (liftedRingedSite S) where
  base := Scheme.smallEtalePullback f
  isMorphismOfSites := inferInstance
  structureSheafMap :=
    (sheafCompose S.smallEtaleTopology
      (Scheme.Site.ringUniverseLift.{u, u + 1})).map (ringedHom f).structureSheafMap

end Small
end Etale
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme
namespace Etale

/-- The base functor of `Small.liftedRingedHom f` is small étale base change along `f`. -/
theorem liftedRingedHom_base {S T : Scheme.{u}} (f : T ⟶ S) :
    (Small.liftedRingedHom f).base = Scheme.smallEtalePullback f := sorry

end Etale
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/-- The assignment from a scheme morphism to its lifted small étale ringed-topos morphism is
faithful up to 2-isomorphism. -/
theorem eq_of_smallEtaleRingedTopos_twoIso {X Y : Scheme.{u}} {a b : X ⟶ Y}
    (h : Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
      (Etale.Small.liftedRingedHom a).toToposHom
      (Etale.Small.liftedRingedHom b).toToposHom)) :
    a = b := sorry

end Hom
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/-- Every `2`-morphism from the lifted small étale ringed-topos morphism induced by a scheme morphism to itself is the identity `2`-morphism. -/
theorem smallEtale_twoMorphism_eq_id {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : RingedSite.ToposHom.TwoMorphism.{u + 1, u, u + 1, u, u + 1}
      (Etale.Small.liftedRingedHom f).toToposHom
      (Etale.Small.liftedRingedHom f).toToposHom) :
    t = RingedSite.ToposHom.TwoMorphism.refl.{u + 1, u, u + 1, u, u + 1} _ := sorry

end Hom
end Scheme
end AlgebraicGeometry
