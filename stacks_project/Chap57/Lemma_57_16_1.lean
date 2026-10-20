/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Koszul.Deformation
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open IsLocalRing
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v

namespace CategoryTheory.DerivedCategory

/- Lemma 57.16.1 -/
@[stacks 0G0N]
#check (CategoryTheory.DerivedCategory.exists_koszul_lift_of_closedFiber :
    ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A]
      [Algebra R A] [IsLocalRing R] [IsLocalRing A]
      [IsLocalHom (algebraMap R A)] [Module.Flat R A],
      RingHom.EssFinitePresentation (algebraMap R A) →
      ∀ {r : ℕ},
        (fbar : Fin r → Ideal.Fiber (maximalIdeal R) A) →
        (∀ i,
          fbar i ∈
            Ideal.map (algebraMap A (Ideal.Fiber (maximalIdeal R) A)) (maximalIdeal A)) →
        RingTheory.Sequence.IsRegular
          (Ideal.Fiber (maximalIdeal R) A) (List.ofFn fbar) →
        (K : DerivedCategory (ModuleCat A)) →
        K.IsPerfect →
        IsIsomorphic
          ((ModuleCat.derivedExtensionOfScalars
            (algebraMap A (Ideal.Fiber (maximalIdeal R) A))).obj K)
          (KoszulComplex.derivedFamily fbar) →
        ∃ f : Fin r → A,
          (∀ i, algebraMap A (Ideal.Fiber (maximalIdeal R) A) (f i) = fbar i) ∧
          RingTheory.Sequence.IsRegular A (List.ofFn f) ∧
          IsIsomorphic K (KoszulComplex.derivedFamily f) ∧
          Module.Flat R (A ⧸ Ideal.span (Set.range f)))

end CategoryTheory.DerivedCategory
