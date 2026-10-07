module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Resolution

@[expose] public section

/-!
# K-Injective Replacements

In an abelian category with enough injectives and exact countable products, every cochain
complex admits a K-injective resolution and a quasi-isomorphism to a K-injective complex.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace KInjectiveResolution

/-- Every cochain complex has a K-injective resolution when the ambient abelian
category has enough injectives and exact countable products. -/
@[stacks 090Y]
theorem nonempty [EnoughInjectives 𝒜] [HasCountableProducts 𝒜]
    [CountableAB4Star 𝒜] (K : CochainComplex 𝒜 ℤ) :
    Nonempty (KInjectiveResolution K) := sorry

end KInjectiveResolution

namespace IsKInjective

/-- In an abelian category with enough injectives and exact countable products,
every cochain complex admits a quasi-isomorphism to a K-injective cochain complex. -/
@[stacks 090Y]
theorem exists_quasiIso [EnoughInjectives 𝒜] [HasCountableProducts 𝒜]
    [CountableAB4Star 𝒜] (K : CochainComplex 𝒜 ℤ) :
    ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (f : K ⟶ I), QuasiIso f := sorry

end IsKInjective

end CochainComplex
