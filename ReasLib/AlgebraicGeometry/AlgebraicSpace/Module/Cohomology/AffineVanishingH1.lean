module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-! # First-cohomology vanishing under affine morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an affine morphism to a quasi-compact, absolutely quasi-separated algebraic
space with vanishing first cohomology, the first cohomology of every quasi-coherent
module on the domain vanishes. -/
theorem cohomology_isZero_of_affine {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u})]
    (f : X' ⟶ X) [Affine f] (F : Modules X')
    (hF : quasiCoherentModuleProperty X' F) : IsZero (cohomology X' F 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
