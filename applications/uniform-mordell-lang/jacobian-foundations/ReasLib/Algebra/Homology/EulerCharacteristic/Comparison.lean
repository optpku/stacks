/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Comparisons for the canonical graded Euler characteristic

The datum is Mathlib's `GradedObject.eulerChar`; this file defines no second Euler
characteristic. Degreewise module isomorphisms transport its rank support and value.
A vanishing bound gives a finite truncation in arbitrary dimension.

Consumers include cohomology of proper schemes, perfect complexes in families,
duality computations and curve Riemann–Roch. A comparison of cohomology models
must supply actual linear isomorphisms before these numerical lemmas apply.

These algebraic identities do not assert finite-dimensionality. As in Mathlib,
`finrank` and `finsum` have junk values outside their finite ranges. Finiteness and
geometric vanishing belong to the theorem computing the cohomology model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace GradedObject

universe u v

variable {R : Type u} [Ring R] {ι : Type v}

/-- A degreewise module isomorphism preserves the support of the finite ranks. -/
theorem finrankSupport_eq_of_iso
    {X Y : CategoryTheory.GradedObject ι (ModuleCat R)} (e : ∀ i, X i ≅ Y i) :
    finrankSupport X = finrankSupport Y := by
  ext i
  simp only [finrankSupport, Function.mem_support, (e i).toLinearEquiv.finrank_eq]

/-- Euler characteristics are invariant under degreewise module isomorphisms,
for any complex shape, coefficient ring and index type. -/
theorem eulerChar_eq_of_iso (c : ComplexShape ι) [c.EulerCharSigns]
    {X Y : CategoryTheory.GradedObject ι (ModuleCat R)} (e : ∀ i, X i ≅ Y i) :
    eulerChar c X = eulerChar c Y := by
  unfold eulerChar
  congr 1
  funext i
  rw [(e i).toLinearEquiv.finrank_eq]

/-- A bound on the actual zero objects, rather than on a chosen curve presentation,
converts the canonical Euler characteristic into a finite sum. -/
theorem eulerChar_eq_sum_range_of_isZero
    [Nontrivial R]
    (X : CategoryTheory.GradedObject ℕ (ModuleCat R)) (n : ℕ)
    (h : ∀ i, n ≤ i → IsZero (X i)) :
    eulerChar (up ℕ) X =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (Module.finrank R (X i) : ℤ) := by
  have hs : finrankSupport X ⊆ (Finset.range n : Set ℕ) := by
    rw [finrankSupport_subset_iff]
    intro i hi
    have hn : n ≤ i := Nat.le_of_not_lt (by simpa using hi)
    letI : Subsingleton (X i) := ModuleCat.isZero_iff_subsingleton.mp (h i hn)
    exact Module.finrank_zero_of_subsingleton
  simpa using eulerChar_eq_sum_finSet_of_finrankSupport_subset (up ℕ) X (Finset.range n) hs

end GradedObject
