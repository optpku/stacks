/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Conservativity of Derived Cohomology

@stack 015C

This leaf records the standard jointly conservative family of cohomology
functors on a derived category.  It is independent of boundedness choices and
is therefore owned by the derived-category homology layer rather than by a
particular Chapter 13 application.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 015C: a morphism in `DerivedCategory 𝒜` is invertible exactly when
every cohomology functor maps it to an isomorphism. -/
@[stacks 015C]
theorem isIso_iff_homology_map_isIso
    {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map f) := sorry

end DerivedCategory

end CategoryTheory
