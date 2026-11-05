/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ReasLib.Algebra.Homology.EulerCharacteristic.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Euler comparisons for canonical ordinary cohomology

These lemmas use Mathlib's graded Euler characteristic directly. They define no
additional numerical invariant. The construction and comparison require no
properness or coherence assumptions; those enter the geometric finiteness
theorems that interpret the value as the usual Euler characteristic.

Keeping this leaf separate lets higher-dimensional cohomology, complexes in
families and curve RR use the numerical comparison without importing the
unfinished geometric finiteness or coherence comparison certificates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The canonical graded Euler value of cohomology is invariant under an actual
coefficient-sheaf isomorphism, without geometric hypotheses. -/
theorem cohomologyEulerChar_eq_of_iso
    (f : X ⟶ Spec (CommRingCat.of k)) {F G : X.Modules} (e : F ≅ G) :
    GradedObject.eulerChar (ComplexShape.up ℕ) (fun i => cohomology f F i) =
      GradedObject.eulerChar (ComplexShape.up ℕ) (fun i => cohomology f G i) :=
  GradedObject.eulerChar_eq_of_iso (ComplexShape.up ℕ)
    (fun i => (cohomologyFunctor f i).mapIso e)

/-- A cohomological vanishing bound computes the Euler value in any dimension. -/
theorem cohomologyEulerChar_eq_sum_range
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (n : ℕ)
    (h : ∀ i, n ≤ i → Limits.IsZero (cohomology f F i)) :
    GradedObject.eulerChar (ComplexShape.up ℕ) (fun i => cohomology f F i) =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (cohomologyFinrank f F i : ℤ) :=
  GradedObject.eulerChar_eq_sum_range_of_isZero _ n h

/-- The two-term Euler formula, with the required higher vanishing explicit. -/
theorem cohomologyEulerChar_eq_finrank_zero_sub_one
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules)
    (h : ∀ i, 2 ≤ i → Limits.IsZero (cohomology f F i)) :
    GradedObject.eulerChar (ComplexShape.up ℕ) (fun i => cohomology f F i) =
      (cohomologyFinrank f F 0 : ℤ) - (cohomologyFinrank f F 1 : ℤ) := by
  rw [cohomologyEulerChar_eq_sum_range f F 2 h]
  simp [Finset.sum_range_succ, sub_eq_add_neg]

end AlgebraicGeometry.Scheme.Hom
