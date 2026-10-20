/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Shift

/-!
# Tor-amplitude in distinguished triangles

Exact fixed-right derived tensoring sends distinguished triangles to distinguished triangles.
The standard t-structure bounds can therefore be propagated one endpoint at a time, and the
interval statements follow by combining the lower and upper APIs.

@stack 0655
@stack 08G2
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.DerivedTensor

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [Right.Has (C := C)]

namespace TorAmplitude.Lower

/-- The lower Tor-amplitude bound on the third vertex of a distinguished triangle. -/
@[stacks 08G2 "lower Tor-amplitude, third vertex"]
theorem obj₃_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a : ℤ}
    (h₁ : HasTorAmplitudeGE T.obj₁ (a + 1)) (h₂ : HasTorAmplitudeGE T.obj₂ a) :
    HasTorAmplitudeGE T.obj₃ a := sorry
/- Proof strategy: tensor the distinguished triangle with each degree-zero test object and apply
the third-vertex `IsGE` theorem to the resulting distinguished triangle. -/

/-- The lower Tor-amplitude bound on the second vertex of a distinguished triangle. -/
@[stacks 08G2 "lower Tor-amplitude, middle vertex"]
theorem obj₂_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a : ℤ}
    (h₁ : HasTorAmplitudeGE T.obj₁ a) (h₃ : HasTorAmplitudeGE T.obj₃ a) :
    HasTorAmplitudeGE T.obj₂ a := sorry
/- Proof strategy: tensor with each degree-zero test object and apply the middle-vertex `IsGE`
two-out-of-three theorem. -/

/-- The lower Tor-amplitude bound on the first vertex of a distinguished triangle. -/
@[stacks 08G2 "lower Tor-amplitude, first vertex"]
theorem obj₁_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a : ℤ}
    (h₂ : HasTorAmplitudeGE T.obj₂ (a + 1)) (h₃ : HasTorAmplitudeGE T.obj₃ a) :
    HasTorAmplitudeGE T.obj₁ (a + 1) := sorry
/- Proof strategy: tensor with each degree-zero test object and apply the first-vertex `IsGE`
two-out-of-three theorem. -/

end TorAmplitude.Lower

namespace TorAmplitude.Upper

/-- The upper Tor-amplitude bound on the third vertex of a distinguished triangle. -/
@[stacks 08G2 "upper Tor-amplitude, third vertex"]
theorem obj₃_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {b : ℤ}
    (h₁ : HasTorAmplitudeLE T.obj₁ (b + 1)) (h₂ : HasTorAmplitudeLE T.obj₂ b) :
    HasTorAmplitudeLE T.obj₃ b := sorry
/- Proof strategy: tensor the distinguished triangle with each degree-zero test object and apply
the third-vertex `IsLE` theorem. -/

/-- The upper Tor-amplitude bound on the second vertex of a distinguished triangle. -/
@[stacks 08G2 "upper Tor-amplitude, middle vertex"]
theorem obj₂_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {b : ℤ}
    (h₁ : HasTorAmplitudeLE T.obj₁ b) (h₃ : HasTorAmplitudeLE T.obj₃ b) :
    HasTorAmplitudeLE T.obj₂ b := sorry
/- Proof strategy: tensor with each degree-zero test object and apply the middle-vertex `IsLE`
two-out-of-three theorem. -/

/-- The upper Tor-amplitude bound on the first vertex of a distinguished triangle. -/
@[stacks 08G2 "upper Tor-amplitude, first vertex"]
theorem obj₁_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {b : ℤ}
    (h₂ : HasTorAmplitudeLE T.obj₂ (b + 1)) (h₃ : HasTorAmplitudeLE T.obj₃ b) :
    HasTorAmplitudeLE T.obj₁ (b + 1) := sorry
/- Proof strategy: tensor with each degree-zero test object and apply the first-vertex `IsLE`
two-out-of-three theorem. -/

end TorAmplitude.Upper

/-- Lower Tor-amplitude bounds are closed under extensions. -/
@[stacks 08G2 "lower Tor-amplitude extension closure"]
instance torAmplitudeGE_isTriangulatedClosed₂ (a : ℤ) :
    (torAmplitudeGE (C := C) a).IsTriangulatedClosed₂ := sorry
/- Proof strategy: package `TorAmplitude.Lower.obj₂_of_distinguished` as extension closure. -/

/-- Upper Tor-amplitude bounds are closed under extensions. -/
@[stacks 08G2 "upper Tor-amplitude extension closure"]
instance torAmplitudeLE_isTriangulatedClosed₂ (b : ℤ) :
    (torAmplitudeLE (C := C) b).IsTriangulatedClosed₂ := sorry
/- Proof strategy: package `TorAmplitude.Upper.obj₂_of_distinguished` as extension closure. -/

/-- A fixed Tor-amplitude interval is closed under extensions. -/
@[stacks 08G2 "Tor-amplitude interval extension closure"]
instance torAmplitudeIn_isTriangulatedClosed₂ (a b : ℤ) :
    (torAmplitudeIn (C := C) a b).IsTriangulatedClosed₂ := sorry
/- Proof strategy: combine the lower- and upper-bound extension-closure instances pointwise. -/

/-- The finite-Tor-dimension property contains a zero object. -/
@[stacks 08G2 "finite Tor dimension contains zero"]
instance finiteTorDimension_containsZero :
    (finiteTorDimension (C := C)).ContainsZero := sorry
/- Proof strategy: choose any interval for a zero object and use vanishing of all its tensor
tests. -/

/-- Finite Tor dimension is closed under extensions. -/
@[stacks 08G2 "finite Tor dimension extension closure"]
instance finiteTorDimension_isTriangulatedClosed₂ :
    (finiteTorDimension (C := C)).IsTriangulatedClosed₂ := sorry
/- Proof strategy: choose intervals for the outer vertices, enlarge both to one common interval,
and apply `TorAmplitude.obj₂_of_distinguished`. -/

/-- Objects of finite Tor dimension form a triangulated object property. -/
@[stacks 08G2 "finite-Tor-dimension triangulated property"]
instance finiteTorDimension_isTriangulated :
    ObjectProperty.IsTriangulated (finiteTorDimension (C := C)) := sorry
/- Proof strategy: combine contains-zero, shift-stability, isomorphism-stability, and extension
closure using the standard `ObjectProperty.IsTriangulated` constructor. -/

namespace TorAmplitude

/-- Lemma 15.67.5 (1) (Stacks `0655`), equivalently Lemma 21.46.6 (1): the first two
Tor-amplitude bounds in a distinguished triangle give the bound on the third vertex. -/
@[stacks 0655 "(1), abstract monoidal form", stacks 08G2 "(1), abstract monoidal form"]
theorem obj₃_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a b : ℤ}
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := sorry
/- Proof strategy: apply the lower- and upper-bound third-vertex theorems and combine the two
bounds with `hasTorAmplitudeIn_iff`. -/

/-- Lemma 15.67.5 (2) (Stacks `0655`), equivalently Lemma 21.46.6 (2): equal Tor-amplitude
bounds on the outer vertices give the same bound on the middle vertex. -/
@[stacks 0655 "(2), abstract monoidal form", stacks 08G2 "(2), abstract monoidal form"]
theorem obj₂_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a b : ℤ}
    (h₁ : HasTorAmplitudeIn T.obj₁ a b) (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := sorry
/- Proof strategy: apply the lower- and upper-bound middle-vertex theorems and combine the two
bounds with `hasTorAmplitudeIn_iff`. -/

/-- Lemma 15.67.5 (3) (Stacks `0655`), equivalently Lemma 21.46.6 (3): the last two
Tor-amplitude bounds give the shifted bound on the first vertex. -/
@[stacks 0655 "(3), abstract monoidal form", stacks 08G2 "(3), abstract monoidal form"]
theorem obj₁_of_distinguished
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) {a b : ℤ}
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := sorry
/- Proof strategy: apply the lower- and upper-bound first-vertex theorems and combine the two
bounds with `hasTorAmplitudeIn_iff`. -/

end TorAmplitude

end

end CategoryTheory.DerivedCategory.DerivedTensor
