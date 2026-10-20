/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Tensor

@[expose] public section

open CategoryTheory
open DerivedCategory
open DerivedCategory.DerivedTensor
open DerivedCategory.DerivedTensor.Bifunctor.Right
open DerivedCategory.DerivedTensor.Right

universe u

/- Lemma 51.5.9 (1): the canonical comparison from `RΓ_T(A) ⊗[A]^L K` to `RΓ_T(K)` is invertible. -/
@[stacks 0EF7] #check (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparison_isIso :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K : DerivedCategory (ModuleCat.{u} A)),
    IsIso (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparison
      T hT hfinite K))

/- Lemma 51.5.9 (2): the canonical comparison from `K ⊗[A]^L RΓ_T(L)` to
`RΓ_T(K ⊗[A]^L L)` is invertible. -/
@[stacks 0EF7]
#check (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparisonRight_isIso :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)),
    IsIso (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparisonRight
      T hT hfinite K L))

/- Lemma 51.5.9 (3): the canonical comparison from `RΓ_T(K) ⊗[A]^L L` to
`RΓ_T(K ⊗[A]^L L)` is invertible. -/
@[stacks 0EF7]
#check (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparisonLeft_isIso :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)),
    IsIso (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparisonLeft
      T hT hfinite K L))

/- Lemma 51.5.9 (4): the canonical comparison from
`RΓ_T(K) ⊗[A]^L RΓ_T(L)` to `RΓ_T(K ⊗[A]^L L)` is invertible. -/
@[stacks 0EF7]
#check (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparisonBoth_isIso :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A)),
    IsIso (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensorComparisonBoth
      T hT hfinite K L))

/- Lemma 51.5.9 (5): if either `K` or `L` has cohomology supported on `T`, then their derived
tensor product also has cohomology supported on `T`. -/
@[stacks 0EF7]
#check (CategoryTheory.ModuleCat.SupportedOn.DerivedSections.tensor_mem :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hKL : DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) K ∨
      DerivedCategory.cohomologyIn (ModuleCat.supportedOn T) L),
    DerivedCategory.cohomologyIn (ModuleCat.supportedOn T)
      (DerivedTensor.Right.obj K L))
