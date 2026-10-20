/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Curves after field extension

This file records dimension, global-sections, and genus preservation under extension of the
ground field.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (X : SchemeOverField k) [IsProper X.hom]

/-- A proper one-dimensional scheme over a field remains one-dimensional after field extension
when its global functions are the ground field. -/
theorem baseChange_topologicalKrullDim_eq_one
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    topologicalKrullDim (FieldExtension.baseChange k K X.hom) = 1 := sorry

/-- The canonical map from an extended ground field to the global functions of the base-changed
scheme is bijective when the original global functions are the ground field. -/
theorem baseChange_globalSectionsMap_bijective
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    Function.Bijective
      (Scheme.Hom.globalSectionsMap (FieldExtension.toBase k K X.hom)) := sorry

/-- The degree-one structure-sheaf cohomology finrank is invariant under extension of the ground
field for a proper one-dimensional scheme with the expected global functions. -/
theorem baseChange_genus_eq
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    Scheme.Hom.cohomologyFinrank (FieldExtension.toBase k K X.hom)
        (SheafOfModules.unit
          (FieldExtension.baseChange k K X.hom).ringCatSheaf :
            (FieldExtension.baseChange k K X.hom).Modules) 1 =
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

end AlgebraicGeometry.SchemeOverField
