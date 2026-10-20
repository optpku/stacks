/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Injectivity and Limits

This leaf records closure of K-injective cochain complexes under a supplied
limit cone.  It deliberately asks for the universal-property witness instead
of choosing a product, so it applies to every concrete model of a limit.
-/

open CategoryTheory CategoryTheory.Limits

universe u v uJ

namespace CochainComplex.IsKInjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 0BK6: a limit of K-injective cochain complexes is K-injective when its supplied
limit cone has the stated universal property. -/
@[stacks 0BK6]
theorem of_isLimit {J : Type uJ} {I : J → CochainComplex 𝒜 ℤ}
    {L : CochainComplex 𝒜 ℤ} (π : ∀ j, L ⟶ I j)
    [∀ j, (I j).IsKInjective] (hπ : IsLimit (Fan.mk L π)) :
    L.IsKInjective := sorry

/-- Products of K-injective cochain complexes are K-injective. -/
@[stacks 0BK6, instance]
theorem product {J : Type uJ} (I : J → CochainComplex 𝒜 ℤ)
    [HasProduct I] [∀ j, (I j).IsKInjective] :
    IsKInjective (∏ᶜ I) := sorry

section ProductInstanceCheck

variable {J : Type uJ} (I : J → CochainComplex 𝒜 ℤ)
  [HasProduct I] [∀ j, (I j).IsKInjective]

#synth IsKInjective (∏ᶜ I)

end ProductInstanceCheck

end CochainComplex.IsKInjective
