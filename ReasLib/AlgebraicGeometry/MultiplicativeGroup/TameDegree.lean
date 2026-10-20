module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TamePoints
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FiniteField.FrobeniusDegree
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.FieldTheory.Perfect

/-! Geometric-Frobenius normalization through the specified completion map. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.PreGaloisCategory
noncomputable section
open ProfiniteGrp (integerGroup hatZ hatZNatCast)

namespace MultiplicativeGroupTame

variable (p : ℕ) [Fact p.Prime]

/-- The specified geometric Frobenius acts by inverse p-power on constant fibers. -/
def primeGeometric (s : GeometricPoint (Spec (.of (ZMod p)))) : Aut s.finiteFiber :=
  Scheme.FiniteEtale.FiniteField.geometricFrobenius p s

abbrev constantGroup (s : GeometricPoint (Spec (.of (ZMod p)))) : ProfiniteGrp.{1} :=
  ProfiniteGrp.of (Aut s.finiteFiber)

/-- Powers of the actual geometric Frobenius give the dense cyclic input to completion. -/
def cyclicFrobenius (s : GeometricPoint (Spec (.of (ZMod p)))) :
    integerGroup.{1} ⟶ GrpCat.of (constantGroup p s) :=
  GrpCat.ofHom
    { toFun := fun n ↦ primeGeometric p s ^ n.toAdd.down
      map_one' := by simp
      map_mul' := by intro m n; exact zpow_add _ _ _ }

/-- The universal continuous extension, with specified values on every integer. -/
def completionFrobenius (s : GeometricPoint (Spec (.of (ZMod p)))) :
    hatZ.{1} ⟶ constantGroup p s :=
  ProfiniteGrp.ProfiniteCompletion.lift (cyclicFrobenius p s)

theorem completionFrobenius_nat (s : GeometricPoint (Spec (.of (ZMod p)))) (n : ℕ) :
    completionFrobenius p s (hatZNatCast n) = primeGeometric p s ^ n := by
  have h := ConcreteCategory.congr_hom
    (ProfiniteGrp.ProfiniteCompletion.lift_eta (cyclicFrobenius p s))
    (Multiplicative.ofAdd (ULift.up (n : ℤ)))
  change completionFrobenius p s (hatZNatCast n) = primeGeometric p s ^ (n : ℤ) at h
  simpa only [zpow_natCast] using h

/-- The reverse map evaluates the actual finite-field covers in every integer quotient. -/
def normalizeDegree (s : GeometricPoint (Spec (.of (ZMod p)))) :
    constantGroup p s ⟶ hatZ.{1} :=
  Scheme.FiniteEtale.FiniteField.normalizeDegree p s

/-- The scalar backend uses exactly the specified geometric Frobenius action. -/
theorem primeGeometric_eq_canonical (s : GeometricPoint (Spec (.of (ZMod p)))) :
    primeGeometric p s = Scheme.FiniteEtale.FiniteField.geometricFrobenius p s := rfl

/-- Normalization after the specified completion map is the identity. -/
theorem completionFrobenius_normalizeDegree (s : GeometricPoint (Spec (.of (ZMod p)))) :
    completionFrobenius p s ≫ normalizeDegree p s = 𝟙 hatZ.{1} := sorry

/-- The specified completion map after normalization is the identity. -/
theorem normalizeDegree_completionFrobenius (s : GeometricPoint (Spec (.of (ZMod p)))) :
    normalizeDegree p s ≫ completionFrobenius p s = 𝟙 (constantGroup p s) := sorry

/-- Finite-field evaluations supply the actual inverse of the specified completion map. -/
instance completionFrobenius_isIso (s : GeometricPoint (Spec (.of (ZMod p)))) :
    IsIso (completionFrobenius p s) :=
  ⟨⟨normalizeDegree p s, completionFrobenius_normalizeDegree p s,
    normalizeDegree_completionFrobenius p s⟩⟩

theorem normalizeDegree_geometric (s : GeometricPoint (Spec (.of (ZMod p)))) :
    normalizeDegree p s (primeGeometric p s) = hatZNatCast 1 := by
  rw [← show completionFrobenius p s (hatZNatCast 1) = primeGeometric p s from
    (completionFrobenius_nat p s 1).trans (pow_one _)]
  exact ConcreteCategory.congr_hom (completionFrobenius_normalizeDegree p s) _

/-- Each finite quotient coordinate is the actual finite-field evaluation. -/
@[simp]
theorem normalizeDegree_coordinate (s : GeometricPoint (Spec (.of (ZMod p))))
    (σ : constantGroup p s)
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    (normalizeDegree p s σ).val H =
      Scheme.FiniteEtale.FiniteField.degreeCoordinate p s H σ := rfl

/-- The actual tame degree map, obtained by restricting to constants and normalizing Frobenius. -/
def degreeToIntegers (η : GeometricPoint (space (ZMod p))) :
    fundamentalGroup (ZMod p) η ⟶ hatZ.{1} :=
  ProfiniteGrp.ofHom (degree (ZMod p) η) ≫ normalizeDegree p (constantPoint (ZMod p) η)

/-- The numerical degree map is surjective by the actual forward completion map. -/
theorem degreeToIntegers_surjective (η : GeometricPoint (space (ZMod p))) :
    Function.Surjective (degreeToIntegers p η) := sorry

/-- At a closed point of degree d, the constructed local action has degree d. -/
theorem localFrobenius_degree_nat (x : closedPoints (overField (ZMod p)).left) :
    degreeToIntegers p (pointOver (ZMod p) x) (localFrobenius (ZMod p) x) =
      hatZNatCast ((overField (ZMod p)).hom.residueDegree x.val) := by
  sorry

/-- Any explicit path gives the same numerical degree for the transported action. -/
theorem frobeniusAlong_degree (η : GeometricPoint (space (ZMod p))) (d : ℕ+)
    (x : points (ZMod p) d)
    (t : fiber (ZMod p) (pointOver (ZMod p) x.val) ≅ fiber (ZMod p) η) :
    degreeToIntegers p η (frobeniusAlong (ZMod p) η x.val t) = hatZNatCast d.val := by
  sorry

end MultiplicativeGroupTame
