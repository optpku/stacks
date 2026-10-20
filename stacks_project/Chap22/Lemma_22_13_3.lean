/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism.Right
import StacksCheckRecall

/-!
# Lemma 22.13.3

The reusable right-action/opposite-endomorphism bridge is owned by
`ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism.Right`.
-/

@[expose] public section

universe u v

open CategoryTheory

/- Lemma 22.13.3 (0FQ5): right differential graded `A`-module structures on a fixed cochain
complex are equivalent to genuine DGA morphisms from `A.opposite` to its endomorphism DGA. -/
@[stacks 0FQ5]
#check
  (@DifferentialGradedModule.WithFixedUnderlying.equivActionOn.{u, v} :
    {R : Type u} → [CommRing R] → (A : CochainDGAlgebra.{u, v} R) →
      (K : CochainComplex (ModuleCat.{v} R) ℤ) →
        DifferentialGradedModule.WithFixedUnderlying A
            (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) ≃
          CochainDGAlgebra.Hom A.opposite (CochainComplex.endomorphismDGA K))

/- The raw-family companion keeps the algebra and module carrier universes independent. -/
#check @DifferentialGradedModule.WithFixedUnderlying.equivEndomorphismDGAHom

/- The forward bridge is the Koszul-signed homogeneous action of `A.opposite`. -/
#check @DifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom_apply

/- The inverse bridge constructs the canonical right-module owner directly. -/
#check @DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
