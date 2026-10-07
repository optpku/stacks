module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion

/-!
# Canonical derived Hom and derived completion

This file records the effect of derived completion on canonical derived Hom from an object with
ideal-power-torsion cohomology.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPowerTorsion

open InternalHom

variable {A : Type u} [CommRing A]

/-- Postcomposition by the universal map to derived completion induces an isomorphism on
canonical derived Hom from an object with `I`-power-torsion cohomology. -/
noncomputable instance rHomMapToCompletionIsIso
    (I : Ideal A) (hI : I.FG) (M : IdealPowerTorsion I)
    (L : DerivedCategory (ModuleCat A)) :
    IsIso (RHom.map (𝟙 M.obj) (toDerivedCompletion I hI L)) := sorry

end CategoryTheory.DerivedCategory.IdealPowerTorsion
