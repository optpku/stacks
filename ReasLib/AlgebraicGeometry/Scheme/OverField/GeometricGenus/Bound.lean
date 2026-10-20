/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.SeparableDegree
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Field
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GeometricGenus

/-- The geometric genus of a proper curve over a field is at most the separable degree of
its global-sections field times the dimension of its degree-one structure-sheaf cohomology
over that field. -/
theorem ofCurve_le_finSepDegree_mul_structureSheafH1Finrank
    {k : Type u} [Field k] (C : SchemeOverField k) [Curve C] [IsProper C.hom] :
    -- Local instance justification (noncanonical choice): the algebra action depends on C.hom, which is not recoverable from the global-sections carrier.
    letI : Algebra k (Scheme.globalSectionsRing C.left) :=
      Scheme.Hom.globalSectionsAlgebra C.hom
    -- Local instance justification (defeq pin): use the exact globalSectionsField C.hom structure appearing in the existing geometric-genus bound.
    letI : Field (Scheme.globalSectionsRing C.left) :=
      (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
    ofScheme C (topologicalKrullDim_eq_one C).le ≤
        Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 := sorry

/-- The separable degree of a proper curve's global-sections field, weighted by its
degree-one structure-sheaf cohomology dimension, is at most the corresponding full degree. -/
theorem separableWeightedGenus_le_weightedGenus
    {k : Type u} [Field k] (C : SchemeOverField k) [Curve C] [IsProper C.hom] :
    -- Local instance justification (noncanonical choice): the algebra action depends on C.hom, which is not recoverable from the global-sections carrier.
    letI : Algebra k (Scheme.globalSectionsRing C.left) :=
      Scheme.Hom.globalSectionsAlgebra C.hom
    -- Local instance justification (defeq pin): use the exact globalSectionsField C.hom structure appearing in the existing geometric-genus bound.
    letI : Field (Scheme.globalSectionsRing C.left) :=
      (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
    Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
        Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
          (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 ≤
      Module.finrank k (Scheme.globalSectionsRing C.left) *
        Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
          (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 := by
  -- Local instance justification (noncanonical choice): the algebra action depends on C.hom, which is not recoverable from the global-sections carrier.
  letI : Algebra k (Scheme.globalSectionsRing C.left) :=
    Scheme.Hom.globalSectionsAlgebra C.hom
  -- Local instance justification (defeq pin): use the exact globalSectionsField C.hom structure appearing in the existing geometric-genus bound.
  letI : Field (Scheme.globalSectionsRing C.left) :=
    (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
  -- Local instance justification (search instability): the intrinsic carrier erases C.hom, so supply the existing globalSectionsFiniteDimensional C.hom instance explicitly.
  letI : FiniteDimensional k (Scheme.globalSectionsRing C.left) :=
    AlgebraicGeometry.globalSectionsFiniteDimensional C.hom
  exact Nat.mul_le_mul_right _ (Field.finSepDegree_le_finrank k (Scheme.globalSectionsRing C.left))

/-- The geometric genus of a proper curve is bounded by its separable-degree-weighted
cohomology dimension, which is bounded by the full-degree-weighted cohomology dimension. -/
theorem ofCurve_le_weightedGenus_chain
    {k : Type u} [Field k] (C : SchemeOverField k) [Curve C] [IsProper C.hom] :
    -- Local instance justification (noncanonical choice): the algebra action depends on C.hom, which is not recoverable from the global-sections carrier.
    letI : Algebra k (Scheme.globalSectionsRing C.left) :=
      Scheme.Hom.globalSectionsAlgebra C.hom
    -- Local instance justification (defeq pin): use the exact globalSectionsField C.hom structure appearing in the existing geometric-genus bound.
    letI : Field (Scheme.globalSectionsRing C.left) :=
      (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
    ofScheme C (topologicalKrullDim_eq_one C).le ≤
        Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 ∧
      Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 ≤
        Module.finrank k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 := by
  -- Local instance justification (noncanonical choice): the algebra action depends on C.hom, which is not recoverable from the global-sections carrier.
  letI : Algebra k (Scheme.globalSectionsRing C.left) :=
    Scheme.Hom.globalSectionsAlgebra C.hom
  -- Local instance justification (defeq pin): use the exact globalSectionsField C.hom structure appearing in the existing geometric-genus bound.
  letI : Field (Scheme.globalSectionsRing C.left) :=
    (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
  exact ⟨ofCurve_le_finSepDegree_mul_structureSheafH1Finrank C,
    separableWeightedGenus_le_weightedGenus C⟩

end AlgebraicGeometry.GeometricGenus
