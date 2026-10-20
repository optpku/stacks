/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteTypeInverseSystem

/-!
# Uniform generators for finite-type inverse systems
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace.FiniteTypeInverseSystem

/-- The stages of a compatible finite-type inverse system over the weak-ideal
quotients of a weakly admissible ring admit a uniform finite bound on their
numbers of algebra generators. -/
theorem exists_uniform_generators {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (B : FiniteTypeInverseSystem A) :
    ∃ r : ℕ, ∀ I : (WeakIdealOfDefinition A)ᵒᵖ,
      ∃ f : MvPolynomial (Fin r) (A ⧸ I.unop.ideal) →ₐ[A ⧸ I.unop.ideal]
          B.obj.right.obj I,
        Function.Surjective f :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace.FiniteTypeInverseSystem
