/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TamePoints
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.FieldTheory.Perfect

/-! Geometric-Frobenius normalization through the specified completion map. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.PreGaloisCategory
noncomputable section

namespace MultiplicativeGroupTame

variable (p : ℕ) [Fact p.Prime]

/-- The characteristic of a specified point over Fp follows from its actual structure map. -/
theorem constantPoint_charP (s : GeometricPoint (Spec (.of (ZMod p)))) : CharP s.K p := by
  sorry

/-- The p-th root automorphism of the actual algebraically closed coefficient-point field. -/
def primeGeometricRingEquiv (s : GeometricPoint (Spec (.of (ZMod p)))) : s.K ≃+* s.K :=
  -- Local instance justification (defeq pin): Use the algebraic-closedness structure of this fixed geometric point for its specified Frobenius.
  letI : IsAlgClosed s.K := s.isAlgClosed
  -- Local instance justification (defeq pin): The fixed point over ZMod p carries characteristic p via its actual structure map.
  letI : CharP s.K p := constantPoint_charP p s
  (frobeniusEquiv s.K p).symm

def primeGeometricSpecIso (s : GeometricPoint (Spec (.of (ZMod p)))) :
    Spec (.of s.K) ≅ Spec (.of s.K) :=
  Scheme.Spec.mapIso (primeGeometricRingEquiv p s).toCommRingCatIso.op

theorem primeGeometric_over (s : GeometricPoint (Spec (.of (ZMod p)))) :
    (primeGeometricSpecIso p s).hom ≫ s.hom = s.hom := by
  sorry

/-- Geometric Frobenius acts by the specified inverse p-power automorphism on constant fibers. -/
def primeGeometric (s : GeometricPoint (Spec (.of (ZMod p)))) : Aut s.finiteFiber :=
  pointAut s (primeGeometricSpecIso p s) (primeGeometric_over p s)

abbrev constantGroup (s : GeometricPoint (Spec (.of (ZMod p)))) : ProfiniteGrp.{1} :=
  ProfiniteGrp.of (Aut s.finiteFiber)

/-- The same profinite-integer carrier used by the source degree extension. -/
abbrev integers : ProfiniteGrp.{1} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative (ULift.{1} ℤ)))

def integerNat (n : ℕ) : integers :=
  ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative (ULift.{1} ℤ)))
    (Multiplicative.ofAdd (ULift.up (n : ℤ)))

/-- Powers of the actual geometric Frobenius give the dense cyclic input to completion. -/
def cyclicFrobenius (s : GeometricPoint (Spec (.of (ZMod p)))) :
    GrpCat.of (Multiplicative (ULift.{1} ℤ)) ⟶ GrpCat.of (constantGroup p s) :=
  GrpCat.ofHom
    { toFun := fun n ↦ primeGeometric p s ^ n.toAdd.down
      map_one' := by simp
      map_mul' := by intro m n; exact zpow_add _ _ _ }

/-- The universal continuous extension, with specified values on every integer. -/
def completionFrobenius (s : GeometricPoint (Spec (.of (ZMod p)))) :
    integers ⟶ constantGroup p s :=
  ProfiniteGrp.ProfiniteCompletion.lift (cyclicFrobenius p s)

theorem completionFrobenius_nat (s : GeometricPoint (Spec (.of (ZMod p)))) (n : ℕ) :
    completionFrobenius p s (integerNat n) = primeGeometric p s ^ n := by
  have h := ConcreteCategory.congr_hom
    (ProfiniteGrp.ProfiniteCompletion.lift_eta (cyclicFrobenius p s))
    (Multiplicative.ofAdd (ULift.up (n : ℤ)))
  change completionFrobenius p s (integerNat n) = primeGeometric p s ^ (n : ℤ) at h
  simpa only [zpow_natCast] using h

/-- Finite fields of every degree test this fixed map: inverse Frobenius has order r
on F_(p^r). Hence this map is an isomorphism; no unrelated equivalence is selected. -/
instance completionFrobenius_isIso (s : GeometricPoint (Spec (.of (ZMod p)))) :
    IsIso (completionFrobenius p s) := by
  sorry

/-- Numerical normalization is the inverse of that already specified continuous map. -/
def normalizeDegree (s : GeometricPoint (Spec (.of (ZMod p)))) :
    constantGroup p s ⟶ integers := inv (completionFrobenius p s)

theorem normalizeDegree_geometric (s : GeometricPoint (Spec (.of (ZMod p)))) :
    normalizeDegree p s (primeGeometric p s) = integerNat 1 := by
  rw [← show completionFrobenius p s (integerNat 1) = primeGeometric p s from
    (completionFrobenius_nat p s 1).trans (pow_one _)]
  exact ConcreteCategory.congr_hom (IsIso.hom_inv_id (completionFrobenius p s)) _

/-- The actual tame degree map, obtained by restricting to constants and normalizing Frobenius. -/
def degreeToIntegers (η : GeometricPoint (space (ZMod p))) :
    fundamentalGroup (ZMod p) η ⟶ integers :=
  ProfiniteGrp.ofHom (degree (ZMod p) η) ≫ normalizeDegree p (constantPoint (ZMod p) η)

/-- At a closed point of degree d, the constructed local action has degree d. -/
theorem localFrobenius_degree_nat (x : closedPoints (overField (ZMod p)).left) :
    degreeToIntegers p (pointOver (ZMod p) x) (localFrobenius (ZMod p) x) =
      integerNat ((overField (ZMod p)).hom.residueDegree x.val) := by
  sorry

/-- Any explicit path gives the same numerical degree for the transported action. -/
theorem frobeniusAlong_degree (η : GeometricPoint (space (ZMod p))) (d : ℕ+)
    (x : points (ZMod p) d)
    (t : fiber (ZMod p) (pointOver (ZMod p) x.val) ≅ fiber (ZMod p) η) :
    degreeToIntegers p η (frobeniusAlong (ZMod p) η x.val t) = integerNat d.val := by
  sorry

end MultiplicativeGroupTame
