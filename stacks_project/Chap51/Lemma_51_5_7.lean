/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/- Lemma 51.5.7 (1): for a flat map of Noetherian rings and a specialization-stable
`T ⊆ Spec(A)`, the canonical map
`RΓ_T(K) ⊗[A]ᴸ B ⟶ RΓ_(inverseImageSupport f T)(K ⊗[A]ᴸ B)` is an isomorphism for
`K ∈ D⁺(A)`. -/
@[stacks 0EF5] #check
  (CategoryTheory.ModuleCat.SupportedOn.flatBaseChangeMapIsIsoOfBoundedBelow :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) (hf : f.Flat) (T : Set (PrimeSpectrum A))
      (hT : StableUnderSpecialization T)
      (K : DerivedCategory.Plus (ModuleCat.{u} A)),
      IsIso (CategoryTheory.ModuleCat.SupportedOn.flatBaseChangeMap f hf T K.obj))

/- Lemma 51.5.7 (2): if the source and target Noetherian rings have finite Krull
dimension, the same flat base-change map is an isomorphism for every `K ∈ D(A)`. -/
@[stacks 0EF5] #check
  (CategoryTheory.ModuleCat.SupportedOn.flatBaseChangeMapIsIsoOfFiniteKrullDim :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) (hf : f.Flat) (T : Set (PrimeSpectrum A))
      (hT : StableUnderSpecialization T)
      (hfiniteA : ∃ d : ℕ, Ring.KrullDimLE d A)
      (hfiniteB : ∃ d : ℕ, Ring.KrullDimLE d B)
      (K : DerivedCategory (ModuleCat.{u} A)),
      IsIso (CategoryTheory.ModuleCat.SupportedOn.flatBaseChangeMap f hf T K))

end CategoryTheory.ModuleCat.SupportedOn
