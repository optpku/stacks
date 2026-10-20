/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Node.CoordinateRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open MvPolynomial
open scoped TensorProduct

universe u

noncomputable section

namespace NodeCoordinateRing

variable (k : Type u) [Field k]

/-- The polynomial algebra homomorphism sending the nodal coordinates to their prescribed powers. -/
def powerPolynomialMap (n m : ℕ+) :
    MvPolynomial (Fin 2) k →ₐ[k] Ring k :=
  MvPolynomial.eval₂AlgHom k fun i ↦
    coordinate k i ^ if i = 0 then (n : ℕ) else (m : ℕ)

/-- The polynomial power map evaluated on a coordinate variable. -/
theorem powerPolynomialMap_X (n m : ℕ+) (i : Fin 2) :
    powerPolynomialMap k n m (X i) =
      coordinate k i ^ if i = 0 then (n : ℕ) else (m : ℕ) := sorry

/-- The nodal equation ideal is contained in the kernel of the polynomial power map. -/
theorem ideal_le_powerPolynomialMap_ker (n m : ℕ+) :
    ideal k ≤ RingHom.ker (powerPolynomialMap k n m).toRingHom := sorry

/-- The ring homomorphism induced by the polynomial power map on the nodal quotient. -/
def powerMap (n m : ℕ+) : Ring k →ₐ[k] Ring k :=
  Ideal.Quotient.liftₐ (ideal k) (powerPolynomialMap k n m)
    (ideal_le_powerPolynomialMap_ker k n m)

/-- The nodal power map sends the first coordinate to its `n`-th power. -/
theorem powerMap_apply_zero (n m : ℕ+) :
    powerMap k n m (coordinate k 0) = coordinate k 0 ^ (n : ℕ) := sorry

/-- The nodal power map sends the second coordinate to its `m`-th power. -/
theorem powerMap_apply_one (n m : ℕ+) :
    powerMap k n m (coordinate k 1) = coordinate k 1 ^ (m : ℕ) := sorry

/-- The image of the nodal coordinate sum under the power map. -/
theorem powerMap_apply_branchSum (n m : ℕ+) :
    powerMap k n m (coordinate k 0 + coordinate k 1) =
      coordinate k 0 ^ (n : ℕ) + coordinate k 1 ^ (m : ℕ) := sorry

/-- The explicit target-ring algebra structure induced by the nodal power map. -/
@[reducible]
noncomputable def powerAlgebra (n m : ℕ+) : Algebra (Ring k) (Ring k) :=
  (powerMap k n m).toRingHom.toAlgebra

/-- The structural algebra map of `powerAlgebra` is the nodal power map. -/
theorem powerAlgebra_algebraMap (n m : ℕ+) :
    @algebraMap (Ring k) (Ring k) _ _ (powerAlgebra k n m) =
      (powerMap k n m).toRingHom := sorry

/-- The generic fibre of the nodal power map as a tensor product with the source fraction ring. -/
noncomputable def GenericFiber (n m : ℕ+) :=
  @TensorProduct (Ring k) _ (Ring k) (FractionRing (Ring k)) _ _
    (powerAlgebra k n m).toModule _

/-- The commutative-ring structure on the generic fibre tensor product. -/
noncomputable instance genericFiberCommRing (n m : ℕ+) :
    CommRing (GenericFiber k n m) :=
  @Algebra.TensorProduct.instCommRing
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _

/-- The canonical map from the target nodal ring into the generic fibre. -/
def genericFiberTargetMap (n m : ℕ+) : Ring k →+* GenericFiber k n m :=
  @Algebra.TensorProduct.includeLeftRingHom
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _

/-- The canonical map from the source total fraction ring into the generic fibre. -/
def genericFiberFractionMap (n m : ℕ+) :
    FractionRing (Ring k) →+* GenericFiber k n m :=
  (@Algebra.TensorProduct.includeRight
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _).toRingHom

/-- The target nodal ring algebra structure on the generic fibre. -/
noncomputable instance genericFiberTargetAlgebra (n m : ℕ+) :
    Algebra (Ring k) (GenericFiber k n m) :=
  (genericFiberTargetMap k n m).toAlgebra

/-- The fraction-ring algebra structure on the generic fibre. -/
noncomputable instance genericFiberFractionAlgebra (n m : ℕ+) :
    Algebra (FractionRing (Ring k)) (GenericFiber k n m) :=
  @Algebra.TensorProduct.rightAlgebra
    (Ring k) (Ring k) (FractionRing (Ring k)) _ _ (powerAlgebra k n m) _ _

/-- The generic fibre is finite over the source fraction ring. -/
noncomputable instance genericFiber_moduleFinite (n m : ℕ+) :
    Module.Finite (FractionRing (Ring k)) (GenericFiber k n m) := sorry

/-- The generic fibre is projective over the source fraction ring. -/
noncomputable instance genericFiber_moduleProjective (n m : ℕ+) :
    Module.Projective (FractionRing (Ring k)) (GenericFiber k n m) := sorry

/-- The nodal power map is finite as a ring homomorphism. -/
theorem powerMap_finite (n m : ℕ+) :
    RingHom.Finite (powerMap k n m).toRingHom := sorry

/-- The localization map induced by the nodal power map. -/
def localizedPowerMap (n m : ℕ+) :
    Localization.Away (coordinate k 0 + coordinate k 1) →+*
      Localization.Away (powerMap k n m (coordinate k 0 + coordinate k 1)) :=
  Localization.awayMap (powerMap k n m).toRingHom (coordinate k 0 + coordinate k 1)

/-- The localized power map agrees with the power map on coefficient classes. -/
theorem localizedPowerMap_apply_algebraMap (n m : ℕ+) (a : Ring k) :
    localizedPowerMap k n m
        (algebraMap (Ring k) (Localization.Away (coordinate k 0 + coordinate k 1)) a) =
      algebraMap (Ring k)
        (Localization.Away (powerMap k n m (coordinate k 0 + coordinate k 1)))
        (powerMap k n m a) := sorry

/-- The localization of the nodal power map is finite when both exponents are units. -/
theorem localizedPowerMap_finite (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    RingHom.Finite (localizedPowerMap k n m) := sorry

/-- The localization of the nodal power map is étale when both exponents are units. -/
theorem localizedPowerMap_etale (n m : ℕ+)
    (hn : IsUnit (((n : ℕ) : k))) (hm : IsUnit (((m : ℕ) : k))) :
    RingHom.Etale (localizedPowerMap k n m) := sorry

end NodeCoordinateRing
