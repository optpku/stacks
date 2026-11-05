/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommFiniteCoefficient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricTraceCharacter
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricResidualHomology
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Etale
noncomputable section
universe u

namespace NoncommCharacterRoots
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable (hΛ : IsUnit (Nat.card Λ : k))

abbrev RootValues := Additive (rootsOfUnity (Nat.card Λ) (AlgebraicClosure k))

include hΛ in
/-- Choose only a primitive root, never a cohomology comparison. The power
map below records exactly how this coefficient coordinate is used. -/
theorem existsPrimitive : ∃ ζ : rootsOfUnity (Nat.card Λ) (AlgebraicClosure k),
    IsPrimitiveRoot (ζ : (AlgebraicClosure k)ˣ) (Nat.card Λ) := by
  letI : NeZero (Nat.card Λ : k) := ⟨hΛ.ne_zero⟩
  letI : NeZero (Nat.card Λ) := .of_neZero_natCast k
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure k) (Nat.card Λ)
  refine ⟨hζ.toRootsOfUnity, ?_⟩
  apply IsPrimitiveRoot.coe_units_iff.mp
  simpa using hζ

def primitive : rootsOfUnity (Nat.card Λ) (AlgebraicClosure k) :=
  (existsPrimitive Λ hΛ).choose

theorem primitive_spec : IsPrimitiveRoot
    (primitive Λ hΛ : (AlgebraicClosure k)ˣ) (Nat.card Λ) :=
  (existsPrimitive Λ hΛ).choose_spec

/-- The specified root coordinate is exponentiation of that primitive root. -/
def power : ZMod (Nat.card Λ) →+ RootValues (k := k) Λ where
  toFun z := Additive.ofMul (primitive Λ hΛ ^ z.val)
  map_zero' := sorry
  map_add' := sorry

theorem power_bijective : Function.Bijective (power Λ hΛ) := sorry

def powerEquiv : ZMod (Nat.card Λ) ≃+ RootValues (k := k) Λ :=
  AddEquiv.ofBijective (power Λ hΛ) (power_bijective Λ hΛ)

/-- Turn roots into rational characters through the specified exponent and
the normalized z/n embedding; no arbitrary additive equivalence is chosen. -/
def rootCharacter : RootValues (k := k) Λ →+ AddCircle (1 : ℚ) :=
  (ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ)).comp
    (powerEquiv Λ hΛ).symm.toAddMonoidHom

variable (M : ModuleCat.{u + 1} Λ)

/-- Character values are killed by card Lambda, since this integer kills M. -/
theorem character_killed (χ : CharacterModule M) (m : M) :
    Nat.card Λ • χ m = 0 := by
  rw [← map_nsmul]
  have hm : Nat.card Λ • m = (Nat.card Λ • (1 : Λ)) • m := by
    simpa only [nsmul_one] using (Nat.cast_smul_eq_nsmul Λ (Nat.card Λ) m).symm
  rw [hm, card_nsmul_eq_zero', zero_smul, map_zero]

/-- The normalized Z/n map is injective and covers exactly the n-torsion.
The exponent below is computed independently of this existence statement. -/
theorem normalizedCharacter_preimage (χ : CharacterModule M) (m : M) :
    ∃! z : ZMod (Nat.card Λ),
      ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ) z = χ m := sorry

/-- Compute the exponent from the rational representative in `[0, 1)`.
Since `card Λ` kills the character value, its product with this representative
is an integer. No unproved existence statement is used to supply data. -/
def characterExponent (χ : CharacterModule M) (m : M) : ZMod (Nat.card Λ) :=
  (⌊(Nat.card Λ : ℚ) * (AddCircle.equivIco (1 : ℚ) 0 (χ m) : ℚ)⌋ : ℤ)

theorem characterExponent_spec (χ : CharacterModule M) (m : M) :
    ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ)
      (characterExponent Λ M χ m) = χ m := by
  let n := Nat.card Λ
  have hn : 0 < n := NoncommFiniteCoefficient.card_pos Λ
  let r : ℚ := AddCircle.equivIco (1 : ℚ) 0 (χ m)
  have hr : (r : AddCircle (1 : ℚ)) = χ m := AddCircle.coe_equivIco
  have hnr : ((n : ℚ) * r : AddCircle (1 : ℚ)) = 0 := by
    rw [← nsmul_eq_mul, AddCircle.coe_nsmul, hr]
    exact character_killed Λ M χ m
  obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hnr
  have ha' : (a : ℚ) = (n : ℚ) * r := by simpa using ha
  have hfloor : ⌊(n : ℚ) * r⌋ = a := by rw [← ha']; simp
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  haveI : NeZero n := ⟨hn.ne'⟩
  change (((((⌊(n : ℚ) * r⌋ : ℤ) : ZMod n).val : ℚ) / n : ℚ) :
    AddCircle (1 : ℚ)) = χ m
  rw [hfloor]
  have hv : (((a : ZMod n).val : ℚ)) = ((a % n : ℤ) : ℚ) := by
    exact_mod_cast ZMod.val_intCast (n := n) a
  rw [hv, ← hr, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-(a / n), ?_⟩
  simp only [zsmul_eq_mul, mul_one, Int.cast_neg]
  have he := Int.emod_add_mul_ediv a n
  have heq : ((a % n : ℤ) : ℚ) + (n : ℚ) * ((a / n : ℤ) : ℚ) = a := by
    exact_mod_cast he
  field_simp
  nlinarith [heq]

/-- The actual inverse sends each character value to its unique exponent,
then raises the specified primitive root to that exponent. -/
def characterToRoots (χ : CharacterModule M) : M →+ RootValues (k := k) Λ where
  toFun m := power Λ hΛ (characterExponent Λ M χ m)
  map_zero' := sorry
  map_add' := sorry

def rootsToCharacter (f : M →+ RootValues (k := k) Λ) : CharacterModule M :=
  (rootCharacter Λ hΛ).comp f

def coefficientEquiv : CharacterModule M ≃+ (M →+ RootValues (k := k) Λ) where
  toFun := characterToRoots Λ hΛ M
  invFun := rootsToCharacter Λ hΛ M
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry


end NoncommCharacterRoots
