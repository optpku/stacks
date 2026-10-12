/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# The fpqc sheaf property for freeness at generic points

This module records fpqc descent for the functor detecting fixed-rank freeness near every
generic point of a fibre.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f]

/-- For a finite-type quasicoherent module, the functor detecting fixed-rank freeness near every
fibre generic point is an fpqc sheaf. -/
theorem freeAtGenericPointsFunctor_isSheaf_fpqc
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (freeAtGenericPointsFunctor f ℱ p) := sorry

end AlgebraicGeometry.Scheme.Flattening
