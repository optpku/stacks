/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.SquareZeroComparison

/-!
# Essential square-zero surjections

A non-surjective `H⁻¹(ξ ⊗^L k)` produces a square-zero residue extension of
`A` over `Λ` along which `ξ` becomes zero on naive cotangent complexes.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory
open scoped NaiveCotangent

universe u

noncomputable section

namespace Algebra.NaiveCotangent

variable {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k]
variable [Algebra Λ A] [Algebra A k]

/-- The degree `-1` homology map of derived scalar extension of `ξ` along
`A → k`. -/
def homologyNegOneMap {E : Minus (ModuleCat.{u} A)}
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A) :
    (homologyFunctor (ModuleCat k) (-1)).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).obj
        (Minus.ι.obj E)) ⟶
    (homologyFunctor (ModuleCat k) (-1)).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).obj
        (naiveCotangentObject Λ A)) :=
  (homologyFunctor (ModuleCat k) (-1)).map
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).map ξ)

/-- `homologyNegOneMap ξ` is the homology functor applied to derived
extension of scalars of `ξ`. -/
theorem homologyNegOneMap_eq {E : Minus (ModuleCat.{u} A)}
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A) :
    homologyNegOneMap ξ =
      (homologyFunctor (ModuleCat k) (-1)).map
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).map ξ) :=
  sorry

/-- Let `Λ → A → k` be finite type ring maps of Noetherian rings
with `k ≃ₐ[A] p.ResidueField` for a prime `p` of `A`. Let
`ξ : E ⟶ NL{A⁄Λ}` be a morphism of `D⁻(ModuleCat A)` such that
`H⁻¹(ξ ⊗^L k)` is not surjective. Then there exists a surjection
`π : A' →ₐ[Λ] A` such that `I = ker π` has square zero and is isomorphic to
`k` as an `A`-module, `Ω[A'⁄Λ] ⊗ k = Ω[A⁄Λ] ⊗ k`, and `E ⟶ NL{A⁄A'}` is zero. -/
theorem exists_squareZeroSurjection_of_homology_not_surjective
    [IsNoetherianRing Λ] [IsNoetherianRing A]
    [Algebra Λ k] [IsScalarTower Λ A k]
    [Algebra.FiniteType Λ A] [Algebra.FiniteType A k]
    (p : Ideal A) [p.IsPrime] (hk : k ≃ₐ[A] p.ResidueField)
    (E : Minus (ModuleCat.{u} A))
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A)
    (hξ : ¬ Epi (homologyNegOneMap (k := k) ξ)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra Λ A') (π : A' →ₐ[Λ] A)
      (hπ : π.toRingHom.IsSquareZeroExtension),
      Nonempty ((squareZeroKernelModule π hπ) ≃ₗ[A] k) ∧
        Function.Bijective (kaehlerMapAlong (k := k) π) ∧
        ξ ≫ naiveCotangentMap π = 0 :=
  sorry

end Algebra.NaiveCotangent
