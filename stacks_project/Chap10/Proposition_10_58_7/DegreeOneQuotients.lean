/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Quotient

@[expose] public section

noncomputable section

universe u v

open HomogeneousIdeal

namespace GradedAlgebra.DegreeOneQuotient

variable {R : Type u} {S : Type v} [CommSemiring R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]

/-
API design: the reusable quotient grading, component maps, component equivalences, and descended
algebra structure are owned by `GradedAlgebra.Quotient`.  This source-facing namespace retains only
the degree-one consequences used by Proposition 10.58.7.  The quotient map is the canonical ring
homomorphism `Ideal.Quotient.mk`; no auxiliary base-algebra coercion is exposed in these statements.
-/

-- Local instance justification (defeq pin): `irrelevant 𝒜bar` must use the exact quotient grading
-- structure produced by `GradedAlgebra.Quotient.spanSingletonGradedAlgebra`.
/-- Proposition 10.58.7 (Tag 00K1): the irrelevant ideal of the quotient grading is the image of
the original irrelevant ideal under `S → S ⧸ (a)` for a degree-one element `a`. -/
@[stacks 00K1 "degree-one principal quotient irrelevant ideal"]
theorem irrelevant_eq_map {a : S} (ha : a ∈ 𝒜 1) :
    let I : Ideal S := Ideal.span ({a} : Set S)
    let q : S →+* S ⧸ I := Ideal.Quotient.mk I
    let 𝒜bar : ℕ → Submodule R (S ⧸ I) := GradedAlgebra.Quotient.grading 𝒜 I
    let _ : GradedAlgebra 𝒜bar :=
      GradedAlgebra.Quotient.spanSingletonGradedAlgebra 𝒜 ⟨1, ha⟩
    Ideal.map q (HomogeneousIdeal.irrelevant 𝒜).toIdeal =
      (HomogeneousIdeal.irrelevant 𝒜bar).toIdeal := sorry

-- Local instance justification (defeq pin): the generator package and `irrelevant 𝒜bar` must
-- elaborate against the same explicit quotient graded-algebra structure.
/-- Proposition 10.58.7 (Tag 00K1): quotienting by a degree-one generator preserves a finite
degree-one generating package required by the successor step. -/
@[stacks 00K1 "degree-one principal quotient generator package"]
theorem successorPackage {a : S} (ha : a ∈ 𝒜 1) {s : Finset S}
    (hs : ∀ x ∈ s, x ∈ 𝒜 1)
    (hspan : Ideal.span (Set.insert a (s : Set S)) = 𝒜₊.toIdeal) :
    let I : Ideal S := Ideal.span ({a} : Set S)
    let 𝒜bar : ℕ → Submodule R (S ⧸ I) := GradedAlgebra.Quotient.grading 𝒜 I
    let _ : GradedAlgebra 𝒜bar :=
      GradedAlgebra.Quotient.spanSingletonGradedAlgebra 𝒜 ⟨1, ha⟩
    ∃ u : Finset (S ⧸ I), u.card ≤ s.card ∧
      (∀ x ∈ u, x ∈ 𝒜bar 1) ∧
      Ideal.span (u : Set (S ⧸ I)) = (HomogeneousIdeal.irrelevant 𝒜bar).toIdeal := sorry

end GradedAlgebra.DegreeOneQuotient

#check @GradedAlgebra.DegreeOneQuotient.irrelevant_eq_map
#check @GradedAlgebra.DegreeOneQuotient.successorPackage
#print axioms GradedAlgebra.DegreeOneQuotient.irrelevant_eq_map
#print axioms GradedAlgebra.DegreeOneQuotient.successorPackage
