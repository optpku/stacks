module

public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Galois.IntegralClosure

@[expose] public section

/-!
# Fixed subalgebras of an integral closure

For an algebraic extension `L / K`, the fixed subalgebra of the integral closure of `A` in `L`
maps canonically to the fixed field.  The map and its integral-closure characterization are kept
at the subgroup level so inertia and decomposition specializations can reuse them directly.

@stack 09EH
-/

universe u v w

namespace integralClosure.FixedPoints

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

/-- A fixed element of the integral closure maps to the corresponding fixed field. -/
@[stacks 09EH "fixed subalgebra maps into the fixed field"]
theorem mem_fixedField (H : Subgroup Gal(L/K))
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    algebraMap (integralClosure A L) L x ∈ IntermediateField.fixedField H := sorry

-- Proof strategy: unfold `IntermediateField.mem_fixedField_iff` and the fixed-subalgebra
-- membership condition.  For each `g ∈ H`, apply the ambient map
-- `algebraMap (integralClosure A L) L` to the equality supplied by `x.2` and simplify the
-- canonical Galois action on the integral closure.

/-- The canonical `A`-algebra map from a fixed subalgebra to its fixed field. -/
@[stacks 09EH "fixed subalgebra to fixed field map"]
noncomputable def toFixedField (H : Subgroup Gal(L/K)) :
    FixedPoints.subalgebra A (integralClosure A L) H →ₐ[A]
      IntermediateField.fixedField H :=
  AlgHom.codRestrict
    ((IsScalarTower.toAlgHom A (integralClosure A L) L).comp
      (FixedPoints.subalgebra A (integralClosure A L) H).val)
    (((IntermediateField.fixedField H).toSubalgebra : Subalgebra K L).restrictScalars A)
    (mem_fixedField (A := A) (K := K) (L := L) H)

/-- The algebra structure induced by the canonical fixed-subalgebra map. -/
@[reducible, stacks 09EH "fixed subalgebra to fixed field algebra"]
noncomputable def toFixedFieldAlgebra (H : Subgroup Gal(L/K)) :
    Algebra (FixedPoints.subalgebra A (integralClosure A L) H)
      (IntermediateField.fixedField H) :=
  (toFixedField (A := A) (K := K) (L := L) H).toRingHom.toAlgebra

/-- Evaluating the fixed-subalgebra map in the ambient field recovers the inclusion. -/
@[simp, stacks 09EH "fixed subalgebra to fixed field evaluation"]
theorem toFixedField_apply (H : Subgroup Gal(L/K))
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    (toFixedField (A := A) (K := K) (L := L) H x : L) =
      algebraMap (integralClosure A L) L x := sorry

-- Proof strategy: unfold `toFixedField`; evaluation of `AlgHom.codRestrict`, composition with
-- the fixed-subalgebra inclusion, and coercion from the fixed field all reduce to the ambient
-- algebra map.

/-- The canonical map from the fixed subalgebra to the fixed field is injective. -/
@[stacks 09EH "fixed subalgebra to fixed field injective"]
theorem toFixedField_injective (H : Subgroup Gal(L/K)) :
    Function.Injective (toFixedField (A := A) (K := K) (L := L) H) := sorry

-- Proof strategy: compare two values after coercion to `L`, rewrite them with
-- `toFixedField_apply`, and use injectivity of the integral-closure inclusion into `L` together
-- with subtype extensionality for the fixed subalgebra.

/-- The fixed subalgebra is the integral closure of `A` in the fixed field. -/
@[stacks 09EH "fixed subalgebra is the integral closure in the fixed field"]
theorem isIntegralClosure (H : Subgroup Gal(L/K)) :
    @IsIntegralClosure (FixedPoints.subalgebra A (integralClosure A L) H) A
      (IntermediateField.fixedField H) _ _ _ _
      (toFixedFieldAlgebra (A := A) (K := K) (L := L) H) := sorry

-- Proof strategy: construct `IsIntegralClosure` with `toFixedField_injective`.  For the
-- `isIntegral_iff` field, map an integral fixed-field element into `L`, use the canonical
-- `IsIntegralClosure (integralClosure A L) A L` characterization to obtain an integral-closure
-- representative, and prove that representative is fixed by `H`; the converse follows from
-- integrality of every element of `integralClosure A L` and `toFixedField_apply`.

end integralClosure.FixedPoints
