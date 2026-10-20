/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.Proposition_104_8_4_Forward
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Proposition104.8.4 as a property of its specified canonical forward functor

The source asserts canonical equivalence. The forward data is constructed in
`Forward`; the theorem below states that this actual functor is an equivalence.
Its proof may remain a Statement-stage Prop debt. No inverse objects or
quasi-inverse functor are extracted from that theorem or essential surjectivity.
-/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty RingedSite RingedSite.Hom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- The source's comparison-map quasi-coherence condition is triangulated. -/
instance qcProperty_isTriangulated : (qcProperty X).IsTriangulated := sorry

/-- The exact-derived forward functor carries its actual standard shift maps. -/
instance forwardDerived_commShift : (forwardDerived X).CommShift ℤ := by
  -- Local instance justification (defeq pin): select the standard chaotic-module derived model already fixed in forwardDerived.
  letI := moduleCat_hasDerivedCategory.{u + 1}
    (ofCommRingSheaf ⊥ (affineStructureSheaf X))
  change (forwardModules X).mapDerivedCategory.CommShift ℤ
  infer_instance

/-- Restrict the canonical shift maps to the actual cohomology-in image. -/
instance toDerivedLQCohFbc_commShift : (toDerivedLQCohFbc X).CommShift ℤ :=
  Functor.CommShift.ofComp
    ((DerivedCategory.cohomologyIn (liftedLqcohFbc X)).liftCompιIso
      (QC.inclusion X ⋙ forwardDerived X) (forwardDerived_mem X)) ℤ

/-- Compose with the standard Verdier quotient shift maps. -/
instance toDerivedQCoh_commShift : (toDerivedQCoh X).CommShift ℤ := by
  change (toDerivedLQCohFbc X ⋙ LiftedDerivedQCoh.quotientFunctor X).CommShift ℤ
  infer_instance

/-- The specified functor preserves distinguished triangles. -/
instance toDerivedQCoh_isTriangulated : (toDerivedQCoh X).IsTriangulated := sorry

/-- The specified functor is integer-linear. -/
instance toDerivedQCoh_linear : (toDerivedQCoh X).Linear ℤ := sorry

/-- The specified canonical forward functor is an equivalence.
This is deliberately a Prop theorem, not an inverse-object construction or a
globally registered essential-surjectivity certificate. -/
theorem qcEquivalence : (toDerivedQCoh X).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack
