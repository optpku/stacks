/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveComparison
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Below Injective Resolutions in the Derived Category

This leaf connects the bounded-below homotopy category of injective complexes
with Mathlib's canonical localization
`DerivedCategory.Plus.Qh`.  No chapter-specific bounded-derived model or
silently installed `HasDerivedCategory.standard` instance is used: callers
provide the chosen derived category through `HasDerivedCategory`.

## Main declarations

* `HomotopyCategory.Plus.Injective.toDerived` is the canonical functor
  `K⁺ᵢ(𝒜) ⥤ DerivedCategory.Plus 𝒜`.
* `InjectiveResolutionFunctor.Lift.isEquivalence` specializes the generic
  localization criterion to Mathlib's bounded-below derived category.
* `InjectiveResolutionFunctor.toDerived.isEquivalence_of_resolution` is the reusable
  equivalence criterion, independent of how the resolution functor was made.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

namespace Lift

/-- Every factorization of a functorial bounded-below injective
resolution through the canonical bounded-below localization is an equivalence.
-/
@[stacks 05TK]
theorem isEquivalence (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : DerivedCategory.Plus 𝒜 ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (fac : DerivedCategory.Plus.Qh ⋙ L ≅ J.toFunctor) :
    Functor.IsEquivalence L := sorry

end Lift

namespace toDerived

/-- Once a functorial bounded-below injective resolution has
been fixed, the canonical functor `K⁺ᵢ(𝒜) ⥤ D⁺(𝒜)` is an equivalence. -/
@[stacks 013V]
theorem isEquivalence_of_resolution
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜) :
    Functor.IsEquivalence (HomotopyCategory.Plus.Injective.toDerived 𝒜) := sorry

/-- If `𝒜` has enough injectives, bounded-below injective
complexes compute its bounded-below derived category. -/
@[stacks 013V]
abbrev isEquivalence [EnoughInjectives 𝒜] :
    Functor.IsEquivalence (HomotopyCategory.Plus.Injective.toDerived 𝒜) :=
  HomotopyCategory.Plus.Injective.toDerived.isEquivalence

end toDerived

end CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor
