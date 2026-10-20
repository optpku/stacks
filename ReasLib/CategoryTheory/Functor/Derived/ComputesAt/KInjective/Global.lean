/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Replacement
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Global Right Derived Functors from K-Injective Resolutions

This leaf globalizes the existing pointwise computation API for K-injective cochain complexes.
The resolution hypothesis is expressed through the canonical `KInjectiveResolution` data owner,
not through a repeated raw existential and not as a global typeclass instance.
-/

open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KInjective

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒟']
  [Abelian 𝒜]

/-- Stacks 070K: if every cochain complex has a K-injective resolution, the right-derived
indexing diagrams are essentially constant everywhere. -/
@[stacks 070K]
theorem RightDerived.EverywhereDefined.of_kInjective_resolutions
    (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟')
    (h_resolution :
      ∀ K : CochainComplex 𝒜 ℤ, Nonempty (CochainComplex.KInjectiveResolution K)) :
    RightDerived.EverywhereDefined F (HomotopyCategory.quasiIso 𝒜 (up ℤ)) := sorry

/-- Stacks 070K: the everywhere-definedness criterion produces a total right derived functor
at quasi-isomorphisms. -/
@[stacks 070K]
theorem RightDerived.hasFunctor_of_kInjective_resolutions
    (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟')
    (h_resolution :
      ∀ K : CochainComplex 𝒜 ℤ, Nonempty (CochainComplex.KInjectiveResolution K)) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso 𝒜 (up ℤ)) := sorry

end CategoryTheory.Functor.KInjective
