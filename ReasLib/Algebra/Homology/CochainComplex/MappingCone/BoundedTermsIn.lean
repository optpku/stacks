/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise
public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.Bounded

/-!
# Mapping cones of bounded termwise complexes

The mapping cone construction only uses two pieces of structure from a termwise object property:
closure under binary coproducts and closure under isomorphisms.  Keeping that requirement generic
lets perfect, projective, free, and other bounded-complex APIs share the same theorem.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable (P : ObjectProperty C) [P.IsClosedUnderBinaryCoproducts]
variable [P.IsClosedUnderIsomorphisms]

/-- Mapping cones preserve a termwise object property closed under binary coproducts. -/
theorem termsIn_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.termsIn P K) (hL : CochainComplex.termsIn P L) :
    CochainComplex.termsIn P (mappingCone f) := sorry

/-- Mapping cones preserve bounded termwise object properties. -/
theorem boundedTermsIn_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : boundedTermsIn P K) (hL : boundedTermsIn P L) :
    boundedTermsIn P (mappingCone f) := sorry

end CochainComplex
