module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.DenseSubsite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf

/-!
# The affine comparison for the small étale ringed topos

The dense inclusion of affine étale objects into the small étale site gives a
canonical morphism from the affine ringed topos, carrying the restricted
lifted structure sheaf, to the full small étale ringed topos.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallAffineComparison

/-- The lifted small-étale structure sheaf restricted to affine étale objects. -/
noncomputable def affineStructureSheaf (S : Scheme.{u}) :
    Sheaf (Scheme.AffineEtale.topology S) RingCat.{u + 1} :=
  RingedSite.DenseSubsite.restrictedStructureSheaf
    (Scheme.AffineEtale.Spec S) (Scheme.AffineEtale.topology S)
    S.smallEtaleTopology (Scheme.Etale.Small.liftedStructureSheaf S)

/-- The small affine étale site equipped with the restricted lifted structure sheaf. -/
noncomputable abbrev affineRingedSite (S : Scheme.{u}) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (Scheme.AffineEtale.topology S) (affineStructureSheaf S)

/-- The morphism of topoi induced by the dense inclusion of affine étale objects into the
small étale site. -/
noncomputable def morphismOfTopoi (S : Scheme.{u}) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      S.smallEtaleTopology (Scheme.AffineEtale.topology S) :=
  Functor.IsDenseSubsite.morphismOfTopoiIn (Scheme.AffineEtale.Spec S)

/-- The canonical morphism from the affine small-étale ringed topos to the full small-étale
ringed topos. -/
noncomputable def comparison (S : Scheme.{u}) :
    RingedSite.ToposHom (affineRingedSite S) (Scheme.Etale.Small.liftedRingedSite S) :=
  RingedSite.DenseSubsite.comparison
    (Scheme.AffineEtale.Spec S) (Scheme.AffineEtale.topology S)
    S.smallEtaleTopology (Scheme.Etale.Small.liftedStructureSheaf S)

/-- The underlying morphism of topoi is the dense affine-étale comparison. -/
theorem comparison_toTopos (S : Scheme.{u}) :
    (comparison S).toTopos = morphismOfTopoi S := sorry

/-- The inverse image of the affine small-étale comparison is restriction along the
inclusion of affine étale objects. -/
theorem comparison_inverseImage (S : Scheme.{u}) :
    (comparison S).toTopos.inverseImage =
      (Scheme.AffineEtale.Spec S).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.AffineEtale.topology S) S.smallEtaleTopology := sorry

end AlgebraicGeometry.Scheme.Etale.SmallAffineComparison
