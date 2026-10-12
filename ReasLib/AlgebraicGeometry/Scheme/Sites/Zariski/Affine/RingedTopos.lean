/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.DenseSubsite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallAffineComparison

/-!
# The affine comparison for the small Zariski ringed topos

The dense inclusion of affine opens into the small Zariski site gives a
canonical morphism from the affine ringed topos, carrying the restricted
lifted structure sheaf, to the full small Zariski ringed topos.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison

/-- The lifted small-Zariski structure sheaf restricted to affine opens. -/
noncomputable def affineStructureSheaf (S : Scheme.{u}) :
    Sheaf S.smallAffineZariskiTopology RingCat.{u + 1} :=
  RingedSite.DenseSubsite.restrictedStructureSheaf
    (Scheme.smallAffineZariskiInclusion S) S.smallAffineZariskiTopology
    S.smallZariskiTopology (Scheme.Zariski.Small.liftedStructureSheaf S)

/-- The small affine Zariski site equipped with the restricted lifted structure sheaf. -/
noncomputable abbrev affineRingedSite (S : Scheme.{u}) : RingedSite.{u, u, u + 1} :=
  RingedSite.ofRingSheaf S.smallAffineZariskiTopology (affineStructureSheaf S)

/-- The morphism of topoi induced by the dense inclusion of affine opens into the small
Zariski site. -/
noncomputable def morphismOfTopoi (S : Scheme.{u}) :
    MorphismOfTopoiIn.{u + 1, u, u, u, u + 1}
      S.smallZariskiTopology S.smallAffineZariskiTopology :=
  Functor.IsDenseSubsite.morphismOfTopoiIn (Scheme.smallAffineZariskiInclusion S)

/-- The canonical morphism from the affine small-Zariski ringed topos to the full small-Zariski
ringed topos. -/
noncomputable def comparison (S : Scheme.{u}) :
    RingedSite.ToposHom (affineRingedSite S) (Scheme.Zariski.Small.liftedRingedSite S) :=
  RingedSite.DenseSubsite.comparison
    (Scheme.smallAffineZariskiInclusion S) S.smallAffineZariskiTopology
    S.smallZariskiTopology (Scheme.Zariski.Small.liftedStructureSheaf S)

/-- The underlying morphism of topoi is the dense affine-open comparison. -/
theorem comparison_toTopos (S : Scheme.{u}) :
    (comparison S).toTopos = morphismOfTopoi S := sorry

/-- The inverse image of the affine small-Zariski comparison is restriction along the
inclusion of affine opens. -/
theorem comparison_inverseImage (S : Scheme.{u}) :
    (comparison S).toTopos.inverseImage =
      (Scheme.smallAffineZariskiInclusion S).sheafPushforwardContinuous (Type (u + 1))
        S.smallAffineZariskiTopology S.smallZariskiTopology := sorry

end AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison
