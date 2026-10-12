/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap72.Definition_72_6_9_Principal
public import stacks_project.Chap72.Lemma_72_7_3_Quotient
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-!
# Principal divisor cycles on good integral algebraic spaces

A rational unit on a good integral algebraic space determines an `(n-1)`-cycle
by converting the principal Weil divisor of Spaces over Fields, Definition
72.6.7, into a locally finite cycle on `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable [IsIntegral X]

/-- The ungraded principal divisor cycle of a rational unit on a good integral
algebraic space, obtained by converting the principal Weil divisor of Spaces
over Fields, Definition 72.6.7, into a locally finite cycle on `|X|`. -/
noncomputable def principalDivisorCycle (φ : (RationalFunction X)ˣ) :
    Function.locallyFinsupp (Points X) ℤ :=
  WeilDivisor.toCycle
    (@principalWeilDivisor S X (LocallyOfFiniteType.isLocallyNoetherian f)
      inferInstance φ)

/-- The ungraded principal divisor is the canonical conversion of the
principal Weil divisor to a locally finite cycle. -/
theorem principalDivisorCycle_eq_toCycle (φ : (RationalFunction X)ˣ) :
    principalDivisorCycle f φ =
      WeilDivisor.toCycle
        (@principalWeilDivisor S X (LocallyOfFiniteType.isLocallyNoetherian f)
          inferInstance φ) :=
  rfl

/-- The ungraded principal divisor cycle agrees at generic points of prime
divisors with the coefficients of `WeilDivisor.ofRationalUnit`. -/
theorem principalDivisorCycle_eq_ofRationalUnit (φ : (RationalFunction X)ˣ)
    (Z : PrimeDivisor X) :
    principalDivisorCycle f φ Z.genericPoint =
      (@WeilDivisor.ofRationalUnit S X (LocallyOfFiniteType.isLocallyNoetherian f)
        inferInstance φ).coeff Z :=
  sorry

/-- At a prime divisor, the ungraded principal divisor cycle has coefficient
equal to the order of vanishing of the rational unit. -/
theorem principalDivisorCycle_apply_primeDivisor (φ : (RationalFunction X)ˣ)
    (Z : PrimeDivisor X) :
    principalDivisorCycle f φ Z.genericPoint =
      (@PrimeDivisor.ord S X (LocallyOfFiniteType.isLocallyNoetherian f)
        inferInstance Z φ) :=
  sorry

variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- If `dim_δ(X) = n`, then the ungraded principal divisor cycle lies in
`Z_{n-1}(X)`, by Lemma 82.12.1. -/
theorem principalDivisorCycle_mem (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    principalDivisorCycle f φ ∈ cycleGroup f δ (n - 1) :=
  sorry

/-- The principal divisor of a rational unit on a good integral algebraic space
of `δ`-dimension `n`, regarded as an `(n-1)`-cycle. -/
noncomputable def principalDivisor (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) : cycleGroup f δ (n - 1) :=
  ⟨principalDivisorCycle f φ, principalDivisorCycle_mem f δ n hX φ⟩

/-- The underlying locally finite cycle of a principal divisor is the ungraded
principal divisor cycle. -/
theorem principalDivisor_coe (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ) =
      principalDivisorCycle f φ :=
  sorry

/-- Unfolding of `principalDivisor` to the ungraded principal divisor cycle. -/
theorem principalDivisor_eq (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ) =
      principalDivisorCycle f φ :=
  sorry

/-- At a prime divisor, the principal divisor has coefficient equal to the
order of vanishing of the rational unit. -/
theorem principalDivisor_apply_primeDivisor (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) (Z : PrimeDivisor X) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ)
        Z.genericPoint =
      (@PrimeDivisor.ord S X (LocallyOfFiniteType.isLocallyNoetherian f)
        inferInstance Z φ) :=
  sorry

/-- A principal divisor is an element of `Z_{n-1}(X)`. -/
theorem principalDivisor_mem_cycleGroup (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ) ∈
      cycleGroup f δ (n - 1) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
