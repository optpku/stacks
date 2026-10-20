module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Resolution
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Injective Resolutions

This leaf records functorial properties of a bounded-below injective
resolution before any choice of derived-category localization.
-/

open CategoryTheory

universe v u

namespace CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 014W: a functorial bounded-below injective resolution is exact as a
triangulated functor. Its shift comparison is asserted through the
Prop-valued `Functor.HasTriangulatedStructure` interface, not installed as a
global instance. -/
@[stacks 014W]
theorem exact (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜) :
    J.toFunctor.HasTriangulatedStructure := sorry

end CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor
