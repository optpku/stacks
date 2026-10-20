/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.EssentialSurjection
import StacksCheckRecall

open CategoryTheory DerivedCategory Algebra

universe u

/- Lemma 98.23.2: For finite-type ring maps Λ → A → k with Λ and A Noetherian
and k the residue field of a prime of A, non-surjective degree −1 residue
homology yields a square-zero surjection with residue-field kernel, unchanged
residue Kähler differentials, and vanishing relative cotangent composite. -/
@[stacks 07YL] #check
  (Algebra.NaiveCotangent.exists_squareZeroSurjection_of_homology_not_surjective :
    ∀ {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k]
      [Algebra Λ A] [Algebra A k]
      [IsNoetherianRing Λ] [IsNoetherianRing A]
      [Algebra Λ k] [IsScalarTower Λ A k]
      [Algebra.FiniteType Λ A] [Algebra.FiniteType A k]
      (p : Ideal A) [p.IsPrime] (hk : k ≃ₐ[A] p.ResidueField)
      (E : Minus (ModuleCat.{u} A))
      (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A),
      ¬ Epi (NaiveCotangent.homologyNegOneMap (k := k) ξ) →
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra Λ A') (π : A' →ₐ[Λ] A)
        (hπ : π.toRingHom.IsSquareZeroExtension),
        Nonempty ((NaiveCotangent.squareZeroKernelModule π hπ) ≃ₗ[A] k) ∧
          Function.Bijective (NaiveCotangent.kaehlerMapAlong (k := k) π) ∧
          ξ ≫ NaiveCotangent.naiveCotangentMap π = 0)
