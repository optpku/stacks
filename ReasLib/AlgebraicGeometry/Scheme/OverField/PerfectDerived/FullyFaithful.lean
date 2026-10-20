/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- A field-linear triangulated functor between perfect derived categories of proper schemes
over a field, with regular source, is fully faithful exactly when its maps on all integer
shifted Homs between closed-point residue-field skyscrapers are bijective. -/
theorem fullyFaithful_iff_map_ext_residueFieldSkyscraper
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
    (F : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k] [F.CommShift ℤ]
    [F.IsTriangulated] :
    Nonempty F.FullyFaithful ↔
      ∀ (x x' : X.left) (hx : x ∈ closedPoints X.left) (hx' : x' ∈ closedPoints X.left)
        (i : ℤ),
        Function.Bijective
          (fun f : residueFieldSkyscraper X x hx ⟶ residueFieldSkyscraper X x' hx'⟦i⟧ ↦
            ShiftedHom.map f F) := sorry

/-- A field-linear exact endofunctor of the perfect derived category of a proper regular scheme
that fixes every coherent module with zero-dimensional support is fully faithful. -/
theorem fullyFaithful_of_iso_on_zero_dimensional_support
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Regular X.left]
    (F : PerfectDerived X ⥤ PerfectDerived X) [F.Linear k] [F.CommShift ℤ]
    (h_exact : F.HasTriangulatedStructure)
    (hF : ∀ ℱ : Coh X.left.toRingedSpace,
      topologicalKrullDim (moduleSupport ℱ.obj) = 0 →
        Nonempty (ofCoherentZeroDimSupport X ℱ ≅ F.obj (ofCoherentZeroDimSupport X ℱ))) :
    Nonempty F.FullyFaithful := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
