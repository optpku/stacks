/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Shift
public import ReasLib.CategoryTheory.Pretriangulated.Subcategory.Coproduct

/-!
# Injective amplitude in distinguished triangles

Mapping cones of morphisms between bounded complexes of injectives remain bounded complexes of
injectives.  The endpoint shifts are exposed explicitly, and the union over all finite intervals
is therefore a triangulated object property.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace InjectiveAmplitude

/-- The first two injective-amplitude bounds in a distinguished triangle give the bound on the
third vertex. -/
theorem obj₃_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a b : ℤ}
    (h₁ : HasInjectiveAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasInjectiveAmplitudeIn T.obj₂ a b) :
    HasInjectiveAmplitudeIn T.obj₃ a b := sorry

/-- Equal injective-amplitude bounds on the outer vertices of a distinguished triangle give the
same bound on the middle vertex. -/
theorem obj₂_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a b : ℤ}
    (h₁ : HasInjectiveAmplitudeIn T.obj₁ a b)
    (h₃ : HasInjectiveAmplitudeIn T.obj₃ a b) :
    HasInjectiveAmplitudeIn T.obj₂ a b := sorry

/-- The last two injective-amplitude bounds in a distinguished triangle give the shifted bound
on the first vertex. -/
theorem obj₁_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a b : ℤ}
    (h₂ : HasInjectiveAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasInjectiveAmplitudeIn T.obj₃ a b) :
    HasInjectiveAmplitudeIn T.obj₁ (a + 1) (b + 1) := sorry

end InjectiveAmplitude

/-- The finite-injective-dimension property contains a zero object. -/
instance finiteInjectiveDimension_containsZero :
    (finiteInjectiveDimension (C := C)).ContainsZero := sorry

/-- Finite injective dimension is closed under extensions. -/
instance finiteInjectiveDimension_isTriangulatedClosed₂ :
    (finiteInjectiveDimension (C := C)).IsTriangulatedClosed₂ := sorry

/-- Objects of finite injective dimension form a triangulated object property. -/
instance finiteInjectiveDimension_isTriangulated :
    ObjectProperty.IsTriangulated (finiteInjectiveDimension (C := C)) := sorry

end CategoryTheory.DerivedCategory
