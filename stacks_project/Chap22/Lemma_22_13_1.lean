/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
import StacksCheckRecall

/-!
# Lemma 22.13.1

The reusable fixed-complex endomorphism-action API is owned by
`ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism`.
-/

@[expose] public section

universe u v

open CategoryTheory

/- Lemma 22.13.1 (0FQ3): a left differential graded module structure on a fixed cochain complex
is equivalently a genuine DGA morphism from `A` to its endomorphism DGA. -/
@[stacks 0FQ3]
#check
  (@LeftDifferentialGradedModule.WithFixedUnderlying.equivActionOn.{u, v} :
    {R : Type u} → [CommRing R] → (A : CochainDGAlgebra.{u, v} R) →
      (K : CochainComplex (ModuleCat.{v} R) ℤ) →
        LeftDifferentialGradedModule.WithFixedUnderlying A
            (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) ≃
          CochainDGAlgebra.Hom A (CochainComplex.endomorphismDGA K))

/- The library-facing action API is definitionally a genuine cochain-DGA morphism. -/
#check
  (@LeftDifferentialGradedModule.ActionOn.{u, v} :
    {R : Type u} → [CommRing R] → (A : CochainDGAlgebra.{u, v} R) →
      (K : CochainComplex (ModuleCat.{v} R) ℤ) →
        Type v)

/- The raw-family companion keeps the algebra and module carrier universes independent. -/
#check @LeftDifferentialGradedModule.WithFixedUnderlying.equivEndomorphismDGAHom

/- Endomorphism action data packages canonically as a left differential graded module. -/
#check @EndomorphismDGAHom.toLeftDifferentialGradedModule
