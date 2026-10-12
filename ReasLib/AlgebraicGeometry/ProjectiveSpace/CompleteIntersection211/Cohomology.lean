/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Cohomology of the type (2, 11) complete-intersection curve

This module records the global-sections and coherent cohomology invariants of the
explicit type (2, 11) complete intersection over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211

/-- The canonical map from the field to the global sections of the structure
sheaf of the explicit type (2, 11) complete intersection is bijective. -/
theorem globalSectionsMap_bijective (k : Type u) [Field k] :
    Function.Bijective (Scheme.Hom.globalSectionsMap (hom k)) := sorry

/-- The degree-one cohomology of the structure sheaf has dimension 100 over the
field of definition. -/
theorem cohomologyFinrank_structureSheaf_one (k : Type u) [Field k] :
    Scheme.Hom.cohomologyFinrank (hom k)
        (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) 1 =
      100 :=
  sorry

/-- The degree-zero cohomology of the structure sheaf has dimension one over the
field of definition. -/
theorem cohomologyFinrank_structureSheaf_zero (k : Type u) [Field k] :
    Scheme.Hom.cohomologyFinrank (hom k)
        (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) 0 =
      1 :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211
