/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- An ample invertible module on a proper one-dimensional scheme over a field,
with constant global functions, a regular global section, and vanishing first cohomology, has
relatively very ample sixth tensor power. -/
theorem relativelyVeryAmple_tensorPow_six
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
    (h_regular : ∃ s : L.sections, RingedSpace.IsRegularSection L s)
    (hH1 : IsZero (Scheme.Hom.cohomology X.hom L 1)) :
    RelativelyVeryAmple X.hom (RingedSpace.TensorPower.sheaf L 6) := sorry

/-- An ample globally generated invertible module on a proper one-dimensional scheme over a field,
with constant global functions and vanishing first cohomology, has relatively very ample square
tensor power. -/
theorem relativelyVeryAmple_tensorPow_two
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
    [SheafOfModules.IsGloballyGenerated L]
    (hH1 : IsZero (Scheme.Hom.cohomology X.hom L 1)) :
    RelativelyVeryAmple X.hom (RingedSpace.TensorPower.sheaf L 2) := sorry

end AlgebraicGeometry.SchemeOverField
