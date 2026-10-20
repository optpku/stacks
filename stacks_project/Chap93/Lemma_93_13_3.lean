/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Localization.Smooth
import StacksCheckRecall

/-!
# Smoothness of localization of ring deformation categories

If `k → P` is of finite type and `Spec P ⟶ Spec k` is smooth at all points of
`zeroLocus {g}` for every `g` in a multiplicative subset `S ⊆ P`, then
`localizationBasedFunctor Λ k S` is smooth and induces a bijection on tangent
spaces.
-/

@[expose] public section

open CategoryTheory
open Algebra
open PrimeSpectrum

universe u

/- Lemma 93.13.3: localization of a finite-type `k`-algebra `P` at a
multiplicative subset `S` induces a smooth functor on deformation categories
and an isomorphism on tangent spaces if `Spec P ⟶ Spec k` is smooth at every
point of `zeroLocus {g}` for every `g ∈ S`. -/
@[stacks 0DZ9] #check (FlatAlgebraCat.isSmooth_localizationBasedFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {P : Type u} [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (S : Submonoid P)
    (hS : ∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P),
    BasedFunctor.IsSmooth (FlatAlgebraCat.localizationBasedFunctor Λ k S))

#check (FlatAlgebraCat.bijective_differential_localizationBasedFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {P : Type u} [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (S : Submonoid P)
    (hS : ∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P),
    Function.Bijective
      (BasedFunctor.differential (FlatAlgebraCat.localizationBasedFunctor Λ k S)))

end
