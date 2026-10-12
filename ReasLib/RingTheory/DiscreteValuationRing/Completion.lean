/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Completion.DiscreteValuationRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite extensions of the fraction field of a completed DVR

Finite separable extensions of the fraction field of a completed discrete valuation ring descend
to finite separable extensions of the original fraction field.

@stack 09EJ
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace DVR.Completion

/-- Lemma 15.114.2, Stacks `09EJ`: a finite separable extension of the fraction field of the
maximal-ideal completion of a discrete valuation ring descends to a finite separable extension of
the original fraction field, and scalar extension recovers the given completed-field extension. -/
@[stacks 09EJ "finite separable extensions descend from the completed fraction field"]
theorem existsFiniteSeparableBaseChange
    {A Khat M : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field Khat] [Algebra (AdicCompletion (maximalIdeal A) A) Khat]
    [IsFractionRing (AdicCompletion (maximalIdeal A) A) Khat]
    [Algebra A Khat] [IsScalarTower A (AdicCompletion (maximalIdeal A) A) Khat]
    [Algebra (FractionRing A) Khat] [IsScalarTower A (FractionRing A) Khat]
    [Field M] [Algebra Khat M] [FiniteDimensional Khat M] [Algebra.IsSeparable Khat M] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (FractionRing A) L)
      (_ : FiniteDimensional (FractionRing A) L) (_ : Algebra.IsSeparable (FractionRing A) L),
      Nonempty ((Khat ⊗[FractionRing A] L) ≃ₐ[Khat] M) := sorry
-- Proof strategy: choose a primitive element of the finite separable extension `M / Khat` and
-- approximate its monic minimal polynomial by one over `FractionRing A`, after clearing
-- denominators into `A`.  Apply `IsCompleteLocalRing.existsRoot_of_smallPerturbation` to retain a
-- nearby simple root that still generates `M` over `Khat`.  Let `L` be the corresponding simple
-- extension over `FractionRing A`; equality of minimal-polynomial degrees gives finite
-- dimensionality and reflects separability along the injective completion map.  Finally use the
-- canonical tensor-product lift `Khat ⊗[FractionRing A] L →ₐ[Khat] M`; the generator proves
-- surjectivity and the matching finite dimensions prove injectivity, yielding `AlgEquiv.ofBijective`.

end DVR.Completion
