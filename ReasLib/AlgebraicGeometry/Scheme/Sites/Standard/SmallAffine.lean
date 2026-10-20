module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallAffineComparison
public import ReasLib.CategoryTheory.Category.ULift

/-!
# Small affine Zariski and étale sites

This module packages the small affine Zariski and étale sites of a scheme behind a uniform
selector, together with their topologies and canonical inclusions into the corresponding full
small sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology.Affine

/-- The category underlying the selected small affine site of `S`. -/
def site (τ : SmallStandardTopology) (S : Scheme.{u}) : Cat.{u, u + 1} :=
  match τ with
  | .zariski => Cat.objULift.{u, u, u + 1} S.smallAffineZariskiSite
  | .etale => Cat.of S.AffineEtale

/-- The selected affine site is the small affine Zariski or small affine étale site. -/
theorem site_spec (τ : SmallStandardTopology) (S : Scheme.{u}) :
    site τ S = match τ with
      | .zariski => Cat.objULift.{u, u, u + 1} S.smallAffineZariskiSite
      | .etale => Cat.of S.AffineEtale := sorry

/-- The Grothendieck topology on the selected small affine site. -/
def topology (τ : SmallStandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology (site τ S) :=
  match τ with
  | .zariski =>
      (Cat.ObjULift.down.{u, u, u + 1} S.smallAffineZariskiSite).inducedTopology
        S.smallAffineZariskiTopology
  | .etale => Scheme.AffineEtale.topology S

/-- The selected affine topology is the canonical Zariski or étale affine topology. -/
theorem topology_spec (τ : SmallStandardTopology) (S : Scheme.{u}) :
    topology τ S = match τ with
      | .zariski =>
          (Cat.ObjULift.down.{u, u, u + 1} S.smallAffineZariskiSite).inducedTopology
            S.smallAffineZariskiTopology
      | .etale => Scheme.AffineEtale.topology S := sorry

/-- The inclusion of the selected affine site into the corresponding full small site. -/
def inclusion (τ : SmallStandardTopology) (S : Scheme.{u}) :
    site τ S ⥤ τ.site S :=
  match τ with
  | .zariski =>
      Cat.ObjULift.down.{u, u, u + 1} S.smallAffineZariskiSite ⋙
        Scheme.smallAffineZariskiInclusion S
  | .etale => Scheme.AffineEtale.Spec S

/-- The selected affine inclusion is the canonical Zariski or étale inclusion. -/
theorem inclusion_spec (τ : SmallStandardTopology) (S : Scheme.{u}) :
    inclusion τ S = match τ with
      | .zariski =>
          Cat.ObjULift.down.{u, u, u + 1} S.smallAffineZariskiSite ⋙
            Scheme.smallAffineZariskiInclusion S
      | .etale => Scheme.AffineEtale.Spec S := sorry

/-- The selected affine inclusion is continuous. -/
instance inclusion_isContinuous (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (inclusion τ S).IsContinuous (topology τ S) (τ.topology S) := sorry

/-- The canonical functor from the selected affine site to schemes over `S`. -/
def toOver (τ : SmallStandardTopology) (S : Scheme.{u}) : site τ S ⥤ Over S :=
  inclusion τ S ⋙ τ.toOver S

/-- The affine functor to `Over S` is the selected inclusion followed by the
full-small-site forgetful functor. -/
theorem toOver_spec (τ : SmallStandardTopology) (S : Scheme.{u}) :
    toOver τ S = inclusion τ S ⋙ τ.toOver S := sorry

end AlgebraicGeometry.SmallStandardTopology.Affine
