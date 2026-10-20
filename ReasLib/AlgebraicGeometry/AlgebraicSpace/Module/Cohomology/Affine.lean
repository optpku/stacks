module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces.AffineCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.SpacesEtale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1

/-!
# Cohomology of quasi-coherent modules on affine algebraic spaces

Quasi-coherent modules on affine algebraic spaces have vanishing cohomology in
positive degrees. This applies to restrictions along affine covering families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Higher cohomology of a quasi-coherent module on an affine algebraic space vanishes. -/
theorem higherCohomology_isZero_of_isAffine {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})]
    [IsAffine Y] (F : Y.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (cohomology Y F p) :=
  sorry

/-- The restriction of a quasi-coherent module to each member of an affine covering
has vanishing cohomology in every positive degree. -/
theorem affineCovering_higherCohomology_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V : spacesEtaleSite X} {ι : Type u} {U : ι → spacesEtaleSite X} {f : ∀ i, U i ⟶ V}
    (h : IsAffineCovering U f) (F : V.left.Modules) [F.IsQuasicoherent] (i : ι)
    (p : ℕ) (hp : 0 < p)
    [HasSheafify (smallEtaleTopology (U i).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology (U i).left) AddCommGrpCat.{u})] :
    IsZero (cohomology (U i).left (Modules.restrict F (f i).left) p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
