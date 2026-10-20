module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.StandardAffine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.StandardAffine
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Big

/-!
# Affine standard sites

This module selects the standard-cover topology on affine schemes over a
scheme for each of the five standard topologies.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Affine

/-- The standard-cover topology on affine schemes over `S` associated to `τ`. -/
def topology (τ : StandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology S.AffineOver :=
  match τ with
  | .zariski => Scheme.bigAffineZariskiTopology S
  | .etale => Scheme.affineOverTopology S (S.overGrothendieckTopology @Etale)
  | .smooth => Scheme.Smooth.StandardAffine.topology S
  | .syntomic => Scheme.Syntomic.StandardAffine.topology S
  | .fppf => Scheme.affineOverTopology S (Scheme.fppfTopology.over S)

/-- The Zariski branch of the selected affine standard topology. -/
theorem topology_zariski (S : Scheme.{u}) :
    topology .zariski S = Scheme.bigAffineZariskiTopology S := sorry

/-- The étale branch of the selected affine standard topology. -/
theorem topology_etale (S : Scheme.{u}) :
    topology .etale S =
      Scheme.affineOverTopology S (S.overGrothendieckTopology @Etale) := sorry

/-- The smooth branch of the selected affine standard topology. -/
theorem topology_smooth (S : Scheme.{u}) :
    topology .smooth S = Scheme.Smooth.StandardAffine.topology S := sorry

/-- The syntomic branch of the selected affine standard topology. -/
theorem topology_syntomic (S : Scheme.{u}) :
    topology .syntomic S = Scheme.Syntomic.StandardAffine.topology S := sorry

/-- The fppf branch of the selected affine standard topology. -/
theorem topology_fppf (S : Scheme.{u}) :
    topology .fppf S =
      Scheme.affineOverTopology S (Scheme.fppfTopology.over S) := sorry

end AlgebraicGeometry.StandardTopology.Affine
