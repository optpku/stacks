/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCoefficientRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricTraceCharacter
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricResidualHomology
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

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
    IsPrimitiveRoot (ζ : (AlgebraicClosure k)ˣ) (Nat.card Λ) := sorry

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
    Nat.card Λ • χ m = 0 := sorry

/-- The normalized Z/n map is injective and covers exactly the n-torsion.
This specifies the preimage used by the following inverse map. -/
theorem normalizedCharacter_preimage (χ : CharacterModule M) (m : M) :
    ∃! z : ZMod (Nat.card Λ),
      ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ) z = χ m := sorry

def characterExponent (χ : CharacterModule M) (m : M) : ZMod (Nat.card Λ) :=
  (normalizedCharacter_preimage Λ M χ m).exists.choose

theorem characterExponent_spec (χ : CharacterModule M) (m : M) :
    ActualGeometricTraceCharacter.normalizedCharacter (Nat.card Λ)
      (characterExponent Λ M χ m) = χ m :=
  (normalizedCharacter_preimage Λ M χ m).exists.choose_spec

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
    (γ : Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
    (z : RootValues (k := k) Λ) : RootValues (k := k) Λ :=
  Additive.ofMul ⟨Units.map
    (AmbientGeometry.arithmeticGaloisQuotient X ηbar γ).toRingEquiv.toMonoidHom
    z.toMul.val, by sorry⟩

/-- The character dual of the actual inverse-Tate coefficient is the roots
dual: the inverse twist and contragredient action produce the positive
cyclotomic factor. This compares specified coefficient functions. -/
theorem inverseTate_equivariant
    (N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))))
    [Finite N.obj.V]
    (γ : Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
    (χ : (CompactRepresentation.continuousDual Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
      (CompactRepresentation.finiteCompactification Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
        (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ N))).obj.V)
    (m : N.obj.V) :
    characterToRoots Λ hΛ N.obj.V
      (((CompactRepresentation.continuousDual Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
        (CompactRepresentation.finiteCompactification Λ
          (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
          (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ N))).obj.ρ γ).hom χ).val m =
    rootsTranslate Λ X ηbar γ
      (characterToRoots Λ hΛ N.obj.V χ.val ((N.obj.ρ γ⁻¹).hom m)) := sorry

end ActualCharacterRoots
