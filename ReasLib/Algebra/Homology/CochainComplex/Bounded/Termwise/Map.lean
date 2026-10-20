/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Map
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise

/-!
# Functoriality of bounded termwise object properties

The hypotheses are expressed by inverse images of object properties, so the API applies to
any pair of source and target properties without introducing a bespoke preservation class.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- A functor maps a termwise-`P` cochain complex to a termwise-`Q` complex whenever
`P ≤ Q.inverseImage F`. -/
theorem termsIn_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (hPQ : P ≤ Q.inverseImage F) {K : CochainComplex C ℤ}
    (hK : termsIn P K) :
    termsIn Q ((F.mapHomologicalComplex (up ℤ)).obj K) := sorry

/-- A functor preserving zero morphisms maps a bounded termwise-`P` complex to a bounded
termwise-`Q` complex whenever `P ≤ Q.inverseImage F`. -/
theorem boundedTermsIn_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (hPQ : P ≤ Q.inverseImage F) {K : CochainComplex C ℤ}
    (hK : boundedTermsIn P K) :
    boundedTermsIn Q ((F.mapHomologicalComplex (up ℤ)).obj K) := sorry

end CochainComplex
