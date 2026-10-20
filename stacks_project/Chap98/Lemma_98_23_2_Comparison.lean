/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.SquareZeroComparison

open CategoryTheory Algebra
open scoped TensorProduct

universe u

/- Lemma 98.23.2: The canonical derived cotangent comparison along an algebra
homomorphism is available through the mathematical comparison owner. -/
#check (Algebra.NaiveCotangent.naiveCotangentMap :
  ∀ {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A),
    Algebra.naiveCotangentObject Λ A ⟶
      @Algebra.naiveCotangentObject A' A _ _ π.toRingHom.toAlgebra)

#check (Algebra.NaiveCotangent.squareZeroKernelModule :
  ∀ {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A),
    π.toRingHom.IsSquareZeroExtension → ModuleCat.{u} A)

#check (Algebra.NaiveCotangent.kaehlerMapAlong :
  ∀ {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] {k : Type u} [Field k] [Algebra A k]
    (π : A' →ₐ[Λ] A),
    @TensorProduct A' _ k (Ω[A'⁄Λ]) _ _
      (Algebra.NaiveCotangent.residueAlgebra π).toModule _ →ₗ[k]
      k ⊗[A] Ω[A⁄Λ])
