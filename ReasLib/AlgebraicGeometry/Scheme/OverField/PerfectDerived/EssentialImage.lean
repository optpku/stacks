/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.CoherentModule
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- For proper schemes over a field with regular source, agreement on degree-`0` coherent
modules of zero-dimensional support and full faithfulness of `F` imply
`G.essImage ≤ F.essImage`. -/
theorem essImage_le_of_iso_on_zeroDimensional_coherent
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
    (F G : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k] [G.Linear k]
    (hF_exact : F.HasTriangulatedStructure) (hG_exact : G.HasTriangulatedStructure)
    [F.Full] [F.Faithful]
    (h_agree : ∀ (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      topologicalKrullDim (moduleSupport ℱ) = 0 →
        Nonempty (F.obj (ofCoherentModule X ℱ) ≅ G.obj (ofCoherentModule X ℱ))) :
    G.essImage ≤ F.essImage := sorry

/-- Membership in the essential image of `F` follows pointwise from the corresponding
essential-image containment criterion. -/
theorem mem_essImage_of_mem_essImage
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
    (F G : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k] [G.Linear k]
    (hF_exact : F.HasTriangulatedStructure) (hG_exact : G.HasTriangulatedStructure)
    [F.Full] [F.Faithful]
    (h_agree : ∀ (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      topologicalKrullDim (moduleSupport ℱ) = 0 →
        Nonempty (F.obj (ofCoherentModule X ℱ) ≅ G.obj (ofCoherentModule X ℱ)))
    (N : PerfectDerived Y) (hN : G.essImage N) : F.essImage N := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
