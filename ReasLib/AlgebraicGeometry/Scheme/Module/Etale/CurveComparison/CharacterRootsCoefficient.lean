/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCoefficientRestriction
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

namespace ActualCharacterRoots
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (hΛ : IsUnit (Nat.card Λ : k))

abbrev RootValues := Additive (rootsOfUnity (Nat.card Λ) (AlgebraicClosure k))

include hΛ in
/-- Choose only a primitive root, never a cohomology comparison. The power
map below records exactly how this coefficient coordinate is used. -/
theorem existsPrimitive : ∃ ζ : rootsOfUnity (Nat.card Λ) (AlgebraicClosure k),
    IsPrimitiveRoot (ζ : (AlgebraicClosure k)ˣ) (Nat.card Λ) := by
  letI : NeZero (Nat.card Λ : k) := ⟨hΛ.ne_zero⟩
  have hn : Nat.card Λ ≠ 0 := NeZero.ne _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure k) (Nat.card Λ)
  have hunit := hζ.isUnit_unit hn
  exact ⟨⟨(hζ.isUnit hn).unit, hunit.mem_rootsOfUnity⟩, hunit⟩

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
  have hm : Nat.card Λ • m = 0 := by
    simpa only [smul_assoc, one_smul, zero_smul] using
      congrArg (fun a : Λ ↦ a • m) (card_nsmul_eq_zero' (x := (1 : Λ)))
  rw [← map_nsmul, hm, map_zero]

/-- The normalized Z/n map is injective and covers exactly the n-torsion.
This specifies the preimage used by the following inverse map. -/
theorem normalizedCharacter_preimage (χ : CharacterModule M) (m : M) :
    ∃! z : ZMod (Nat.card Λ),
      ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ) z = χ m := by
  have hn : 0 < Nat.card Λ := Nat.card_pos
  have hq : (0 : ℚ) < Nat.card Λ := by exact_mod_cast hn
  obtain ⟨i, hi, hiχ⟩ :=
    (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) hn).mp (character_killed Λ M χ m)
  have hi' : ActualGeometricTraceCharacter.normalizedCharacter
      (Nat.card Λ) (i : ZMod (Nat.card Λ)) = χ m := by
    change (↑(((i : ZMod (Nat.card Λ)).val : ℚ) / Nat.card Λ) :
      AddCircle (1 : ℚ)) = χ m
    rw [ZMod.val_natCast_of_lt hi]
    simpa only [mul_one] using hiχ
  refine ⟨(i : ZMod (Nat.card Λ)), hi', ?_⟩
  intro z hz
  have hmem (w : ZMod (Nat.card Λ)) :
      (w.val : ℚ) / Nat.card Λ ∈ Set.Ico (0 : ℚ) (0 + 1) := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hq.le
    · rw [zero_add]
      exact (div_lt_one hq).mpr (Nat.cast_lt.mpr w.val_lt)
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (hmem z) (hmem (i : ZMod (Nat.card Λ)))).mp (hz.trans hi'.symm)
  apply ZMod.val_injective (Nat.card Λ)
  exact Nat.cast_injective ((div_left_inj' hq.ne').mp he)

/-- Compute the exponent from the representative in `[0,1)`. This formula
also defines data independently of the torsion and preimage proofs. -/
def characterExponent (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) (χ : CharacterModule M) (m : M) : ZMod (Nat.card Λ) :=
  (⌊(Nat.card Λ : ℚ) *
    (AddCircle.equivIco (1 : ℚ) 0 (χ m) : ℚ)⌋₊ : ℕ)

theorem characterExponent_spec (χ : CharacterModule M) (m : M) :
    ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ)
      (characterExponent Λ M χ m) = χ m := by
  obtain ⟨z, hz, _⟩ := normalizedCharacter_preimage Λ M χ m
  have hn : (0 : ℚ) < Nat.card Λ := by exact_mod_cast (Nat.card_pos (α := Λ))
  have hmem : (z.val : ℚ) / Nat.card Λ ∈ Set.Ico (0 : ℚ) (0 + 1) := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hn.le
    · rw [zero_add]
      exact (div_lt_one hn).mpr (Nat.cast_lt.mpr z.val_lt)
  have he : characterExponent Λ M χ m = z := by
    unfold characterExponent
    rw [← hz]
    change ((⌊(Nat.card Λ : ℚ) *
      (AddCircle.equivIco (1 : ℚ) 0
        (↑((z.val : ℚ) / Nat.card Λ) : AddCircle (1 : ℚ)) : ℚ)⌋₊ : ℕ) :
      ZMod (Nat.card Λ)) = z
    rw [AddCircle.equivIco_coe_eq hmem]
    change ((⌊(Nat.card Λ : ℚ) * ((z.val : ℚ) / Nat.card Λ)⌋₊ : ℕ) :
      ZMod (Nat.card Λ)) = z
    rw [mul_div_cancel₀ _ hn.ne', Nat.floor_natCast, ZMod.natCast_zmod_val]
  rw [he]
  exact hz

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

/-- Scalar compatibility is precomposition on M. Roots are not asserted
to carry a Lambda-module structure. -/
theorem coefficientEquiv_smul (a : Λ) (χ : CharacterModule M) (m : M) :
    coefficientEquiv Λ hΛ M (a • χ) m = coefficientEquiv Λ hΛ M χ (a • m) := sorry

variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- Actual arithmetic action on roots, through the existing Galois quotient. -/
def rootsTranslate
    (γ : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (z : RootValues (k := k) Λ) : RootValues (k := k) Λ :=
  Additive.ofMul ⟨Units.map
    (AmbientGeometry.arithmeticGaloisQuotient X ηbar γ).toRingEquiv.toMonoidHom
    z.toMul.val, by sorry⟩

/-- The character dual of the actual inverse-Tate coefficient is the roots
dual: the inverse twist and contragredient action produce the positive
cyclotomic factor. This compares specified coefficient functions. -/
theorem inverseTate_equivariant
    (N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite N.obj.V]
    (γ : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (χ : (CompactRepresentation.continuousDual Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
      (CompactRepresentation.finiteCompactification Λ
        (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
        (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ N))).obj.V)
    (m : N.obj.V) :
    characterToRoots Λ hΛ N.obj.V
      (((CompactRepresentation.continuousDual Λ
        (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
        (CompactRepresentation.finiteCompactification Λ
          (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
          (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ N))).obj.ρ γ).hom χ).val m =
    rootsTranslate Λ X ηbar γ
      (characterToRoots Λ hΛ N.obj.V χ.val ((N.obj.ρ γ⁻¹).hom m)) := sorry

end ActualCharacterRoots
