/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.Algebra.Homology.CochainComplex.Bounded

/-!
# Bounded-above nonnegative cochain complexes

For a cochain complex indexed by `ℕ`, boundedness is the existence of an upper degree beyond
which all terms are zero objects.  This intrinsic predicate avoids extending a complex to integer
degrees merely to state its support condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex.Nat

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A nonnegative cochain complex is bounded above if its terms are zero objects in all
sufficiently large degrees. -/
@[stacks 013H "bounded-above nonnegative cochain complexes"]
def IsBoundedAbove (K : CochainComplex C ℕ) : Prop :=
  ∃ b : ℕ, ∀ i : ℕ, b < i → IsZero (K.X i)

/-- The pointwise support criterion for boundedness above. -/
theorem isBoundedAbove_iff (K : CochainComplex C ℕ) :
    IsBoundedAbove K ↔ ∃ b : ℕ, ∀ i : ℕ, b < i → IsZero (K.X i) := sorry

/-- A displayed upper bound proves that a nonnegative cochain complex is bounded above. -/
theorem isBoundedAbove_of_bound (K : CochainComplex C ℕ) (b : ℕ)
    (hK : ∀ i : ℕ, b < i → IsZero (K.X i)) : IsBoundedAbove K := sorry

/-- Extending a nonnegative complex by zero to integer degrees identifies intrinsic boundedness
above with the standard `Comp⁻` object property. -/
theorem isBoundedAbove_iff_minus [HasZeroObject C] (K : CochainComplex C ℕ) :
    IsBoundedAbove K ↔ CochainComplex.minus C (K.extend ComplexShape.embeddingUpNat) := sorry

/-- Since extension by zero is automatically bounded below, a nonnegative complex is bounded
above exactly when its integer extension is bounded. -/
theorem isBoundedAbove_iff_bounded [HasZeroObject C] (K : CochainComplex C ℕ) :
    IsBoundedAbove K ↔ CochainComplex.bounded C (K.extend ComplexShape.embeddingUpNat) := sorry

namespace IsBoundedAbove

/-- An intrinsic upper bound on a nonnegative complex gives a strict upper bound on its
extension by zero to integer degrees. -/
theorem exists_extend_isStrictlyLE [HasZeroObject C] {K : CochainComplex C ℕ}
    (hK : IsBoundedAbove K) :
    ∃ b : ℕ,
      CochainComplex.IsStrictlyLE
        (K.extend ComplexShape.embeddingUpNat : CochainComplex C ℤ) (b : ℤ) := sorry

end IsBoundedAbove

end CochainComplex.Nat
