/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant.Swap
import StacksCheckRecall

universe u v

/- Lemma 42.68.15: the determinants of an exact two-periodic endomorphism complex on a
finite-length module and of the complex obtained by swapping its two differentials multiply
to one in the unit group of the residue field. -/
@[stacks 02PL] #check
  (CategoryTheory.TwoPeriodicEndomorphism.determinant_mul_swap :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R))
      (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic),
      CategoryTheory.TwoPeriodicEndomorphism.determinant K hM hK *
        CategoryTheory.TwoPeriodicEndomorphism.determinant
          (CategoryTheory.TwoPeriodicEndomorphism.swap K) hM
          ((CategoryTheory.TwoPeriodicEndomorphism.swap_acyclic_iff K).2 hK) = 1)
