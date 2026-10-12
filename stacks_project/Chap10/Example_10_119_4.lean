/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.LocalRing.Kollar

/-!
# A Power-Series Example of Kollár's Exceptional Extension

This file models `k[[x, y]]/(y ^ 2)` and the finite extension
`k[[x, y]]/(y ^ 2) → k[[x, z]]/(z ^ 2)` induced by `x ↦ x` and `y ↦ x * z`.
The iterated map sends `y` to `x ^ n * z`.

@stack 00PA
-/

@[expose] public section

noncomputable section

universe u

namespace IsLocalRing.Kollar.DualNumberPowerSeries

variable (k : Type u) [Field k]

/-- The ambient power-series ring `k[[x, y]]`. -/
abbrev SourceAmbient : Type u :=
  MvPowerSeries (Fin 2) k

/-- The ambient power-series ring `k[[x, z]]`. -/
abbrev TargetAmbient : Type u :=
  MvPowerSeries Bool k

/-- The source coordinate `x`. -/
def sourceX : SourceAmbient k :=
  MvPowerSeries.X (0 : Fin 2)

/-- The source coordinate `y`. -/
def sourceY : SourceAmbient k :=
  MvPowerSeries.X (1 : Fin 2)

/-- The target coordinate `x`. -/
def targetX : TargetAmbient k :=
  MvPowerSeries.X false

/-- The target coordinate `z`. -/
def targetZ : TargetAmbient k :=
  MvPowerSeries.X true

/-- The source square-zero ideal `(y ^ 2)`. -/
def sourceIdeal : Ideal (SourceAmbient k) :=
  Ideal.span ({sourceY k ^ 2} : Set (SourceAmbient k))

/-- The target square-zero ideal `(z ^ 2)`. -/
def targetIdeal : Ideal (TargetAmbient k) :=
  Ideal.span ({targetZ k ^ 2} : Set (TargetAmbient k))

/-- The source ring `k[[x, y]]/(y ^ 2)`. -/
abbrev SourceRing : Type u :=
  SourceAmbient k ⧸ sourceIdeal k

/-- The target ring `k[[x, z]]/(z ^ 2)`. -/
abbrev TargetRing : Type u :=
  TargetAmbient k ⧸ targetIdeal k

/-- The source quotient is nonzero. -/
instance instNontrivialSourceRing : Nontrivial (SourceRing k) := sorry

/-- The target quotient is nonzero. -/
instance instNontrivialTargetRing : Nontrivial (TargetRing k) := sorry

/-- Example 10.119.4 (1): the source quotient is local. -/
@[stacks 00PA]
instance instIsLocalRingSourceRing : IsLocalRing (SourceRing k) := sorry

/-- Example 10.119.4 (2): the source quotient is Noetherian. -/
@[stacks 00PA]
instance instIsNoetherianRingSourceRing : IsNoetherianRing (SourceRing k) := sorry

/-- The substitution sending the source coordinates to `x` and `x ^ n * z`. -/
def substitution (n : ℕ) : Fin 2 → TargetAmbient k :=
  ![targetX k, targetX k ^ n * targetZ k]

/-- The coordinate substitution is admissible for multivariable formal power series. -/
theorem substitution_hasSubst (n : ℕ) :
    MvPowerSeries.HasSubst (substitution k n) := sorry

/-- The ambient algebra map induced by `x ↦ x` and `y ↦ x ^ n * z`. -/
def ambientMap (n : ℕ) : SourceAmbient k →ₐ[k] TargetAmbient k :=
  MvPowerSeries.substAlgHom (substitution_hasSubst k n)

/-- The ambient substitution followed by the target quotient map. -/
def ambientToTarget (n : ℕ) : SourceAmbient k →+* TargetRing k :=
  (Ideal.Quotient.mk (targetIdeal k)).comp (ambientMap k n).toRingHom

/-- The ambient-to-target map kills the source square-zero ideal. -/
theorem ambientToTarget_eq_zero (n : ℕ) {f : SourceAmbient k}
    (hf : f ∈ sourceIdeal k) :
    ambientToTarget k n f = 0 := sorry

/-- The quotient map modeling the extension obtained by adjoining `y / x ^ n`. -/
def iteratedExtension (n : ℕ) : SourceRing k →+* TargetRing k :=
  Ideal.Quotient.lift (sourceIdeal k) (ambientToTarget k n)
    (fun _ hf ↦ ambientToTarget_eq_zero k n hf)

/-- The extension `k[[x, y]]/(y ^ 2) → k[[x, z]]/(z ^ 2)` with `y ↦ x * z`. -/
def extension : SourceRing k →+* TargetRing k :=
  iteratedExtension k 1

/-- The class of the source coordinate `x`. -/
def sourceXClass : SourceRing k :=
  Ideal.Quotient.mk (sourceIdeal k) (sourceX k)

/-- The class of the source coordinate `y`. -/
def sourceYClass : SourceRing k :=
  Ideal.Quotient.mk (sourceIdeal k) (sourceY k)

/-- The class of the target coordinate `x`. -/
def targetXClass : TargetRing k :=
  Ideal.Quotient.mk (targetIdeal k) (targetX k)

/-- The class of the target coordinate `z`. -/
def targetZClass : TargetRing k :=
  Ideal.Quotient.mk (targetIdeal k) (targetZ k)

/-- The iterated extension fixes the `x` coordinate. -/
@[simp]
theorem iteratedExtension_sourceX (n : ℕ) :
    iteratedExtension k n (sourceXClass k) = targetXClass k := sorry

/-- The iterated extension sends `y` to `x ^ n * z`. -/
@[simp]
theorem iteratedExtension_sourceY (n : ℕ) :
    iteratedExtension k n (sourceYClass k) = targetXClass k ^ n * targetZClass k := sorry

/-- Example 10.119.4 (3): the ring `k[[x, y]]/(y ^ 2)` has Krull dimension one. -/
@[stacks 00PA]
theorem sourceRing_krullDim_eq_one :
    ringKrullDim (SourceRing k) = 1 := sorry

/-- Example 10.119.4 (4): the ring `k[[x, y]]/(y ^ 2)` is Cohen-Macaulay. -/
@[stacks 00PA]
instance instCohenMacaulaySourceRing :
    Module.CohenMacaulay (SourceRing k) (SourceRing k) := sorry

/-- Example 10.119.4 (5): the displayed extension is injective. -/
@[stacks 00PA]
theorem extension_injective :
    Function.Injective (extension k) := sorry

/-- Example 10.119.4 (6): the displayed extension sends `y` to `x * z`. -/
@[stacks 00PA]
theorem extension_sourceY :
    extension k (sourceYClass k) = targetXClass k * targetZClass k := sorry

/-- Example 10.119.4 (7): the displayed map is an exceptional finite extension in the sense of
Lemma 10.119.3. -/
@[stacks 00PA]
theorem extension_isExceptional :
    RingHom.Kollar.IsExceptionalExtension (extension k) := sorry

/-- Example 10.119.4 (8): for `1 < n`, repeating the construction sends `y` to `x ^ n * z`,
equivalently adjoining `y / x ^ n`. -/
@[stacks 00PA]
theorem iteratedExtension_sourceY_of_one_lt (n : ℕ) (hn : 1 < n) :
    iteratedExtension k n (sourceYClass k) = targetXClass k ^ n * targetZClass k := sorry

end IsLocalRing.Kollar.DualNumberPowerSeries

#print axioms IsLocalRing.Kollar.DualNumberPowerSeries.iteratedExtension
#print axioms IsLocalRing.Kollar.DualNumberPowerSeries.extension
