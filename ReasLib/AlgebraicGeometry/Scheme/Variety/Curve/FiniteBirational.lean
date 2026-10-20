/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.RegularLocus

/-!
# Finite birational morphisms of proper regular curves

Ample effective Cartier divisors supported in an isomorphism open descend to the
target curve. The structure-module cokernel controls the global sections of all
integral twists of the descended divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve.FiniteBirational

/-- The target of a finite birational morphism from a proper regular curve admitting
an ample invertible module is proper over the ground field. -/
theorem targetIsProper
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left] :
    IsProper Y.hom := sorry

/-- A finite birational morphism from a proper regular curve admitting an ample
invertible module is the normalization morphism up to an isomorphism over its target. -/
theorem existsNormalizationIso
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left] :
    ∃ e : X.left ≅ Y.left.normalization,
      e.hom ≫ Y.left.normalizationTo = π.left := sorry

/-- The inverse image of a dense isomorphism open under a finite birational morphism
from a proper regular curve admitting an ample invertible module contains an effective
Cartier divisor whose associated invertible module is ample. -/
theorem existsAmpleDivisor
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V)) :
    ∃ (D : X.left.IdealSheafData) (hD : IsEffectiveCartierDivisor D.subschemeι),
      (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left) ∧
        isAmpleObject (associatedSheaf D (hD := hD)) := sorry

/-- The scheme-theoretic image of an effective Cartier divisor supported over a dense
isomorphism open of a finite birational morphism of curves is effective Cartier. -/
theorem imageIsEffectiveCartier
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left)) :
    IsEffectiveCartierDivisor (D.map π.left).subschemeι := sorry

/-- The structure-module map to the pushforward under a finite birational morphism
from a proper regular curve admitting an ample invertible module has coherent cokernel. -/
theorem cokernelIsCoherent
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left] :
    (Limits.cokernel
      (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)).IsCoherent := sorry

/-- The structure-module cokernel of a finite birational morphism of curves is supported
outside any specified dense open over which the morphism is an isomorphism. -/
theorem cokernelSupport_subset
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V)) :
    RingedSpace.moduleSupport
      (Limits.cokernel
        (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)) ⊆
      (V : Set Y.left)ᶜ := sorry

/-- For each integral twist of an effective Cartier divisor supported over a dense
isomorphism open, the descended divisor module injects into the pushforward of the source
divisor module, with cokernel isomorphic to the structure-module cokernel. -/
theorem existsTwistMap
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left))
    [IsEffectiveCartierDivisor (D.map π.left).subschemeι] (n : ℤ) :
    ∃ φ : tensorPowerInt (associatedSheaf (D.map π.left)) n ⟶
        (Scheme.Modules.pushforward π.left).obj (tensorPowerInt (associatedSheaf D) n),
      Mono φ ∧ IsIsomorphic (Limits.cokernel φ)
        (Limits.cokernel
          (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)) := sorry

/-- For integral twists of an effective Cartier divisor supported over a dense
isomorphism open, the signed difference of source and target global-section dimensions
lies between zero and the global-section dimension of the structure-module cokernel. -/
theorem h0DifferenceBounds
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left))
    [IsEffectiveCartierDivisor (D.map π.left).subschemeι] (n : ℤ) :
    0 ≤ (X.hom.cohomologyFinrank (tensorPowerInt (associatedSheaf D) n) 0 : ℤ) -
        (Y.hom.cohomologyFinrank
          (tensorPowerInt (associatedSheaf (D.map π.left)) n) 0 : ℤ) ∧
      (X.hom.cohomologyFinrank (tensorPowerInt (associatedSheaf D) n) 0 : ℤ) -
          (Y.hom.cohomologyFinrank
            (tensorPowerInt (associatedSheaf (D.map π.left)) n) 0 : ℤ) ≤
        (Y.hom.cohomologyFinrank
          (Limits.cokernel
            (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)) 0 : ℤ) := sorry

/-- The descended divisor of an ample effective Cartier divisor supported over a dense
isomorphism open has global-section dimensions eventually exceeding every natural bound. -/
theorem eventuallyH0Ge
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left))
    (hD_ample : isAmpleObject (associatedSheaf D))
    [IsEffectiveCartierDivisor (D.map π.left).subschemeι] (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      N ≤ Y.hom.cohomologyFinrank
        (tensorPowerInt (associatedSheaf (D.map π.left)) (n : ℤ)) 0 := sorry

end AlgebraicGeometry.Curve.FiniteBirational
