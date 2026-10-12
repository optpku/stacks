/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CoordinateCross.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Structure-sheaf cohomology of the coordinate cross

The structure sheaf of the coordinate cross has cohomology `k` in degree zero
and vanishing cohomology in every positive degree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.CoordinateCross

/-- The canonical coefficient map from a field to the global sections of the
coordinate cross is bijective. -/
theorem globalSectionsMap_bijective (k : Type u) [Field k] (n : ℕ) :
    Function.Bijective (Scheme.Hom.globalSectionsMap (toSpec k n)) := sorry

/-- Degree-zero structure-sheaf cohomology of the coordinate cross over a field
`k` is isomorphic to `k` as a `k`-module. -/
theorem cohomology_zero (k : Type u) [Field k] (n : ℕ) :
    IsIsomorphic
      (Scheme.Hom.cohomology (toSpec k n)
        (SheafOfModules.unit (scheme k n).ringCatSheaf : (scheme k n).Modules) 0)
      (ModuleCat.of k k) := sorry

/-- Structure-sheaf cohomology of the coordinate cross over a field vanishes
in every positive degree. -/
theorem cohomology_isZero_of_pos (k : Type u) [Field k] (n i : ℕ) (hi : 0 < i) :
    IsZero
      (Scheme.Hom.cohomology (toSpec k n)
        (SheafOfModules.unit (scheme k n).ringCatSheaf : (scheme k n).Modules) i) := sorry

end AlgebraicGeometry.ProjectiveSpace.CoordinateCross
