/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafPseudofunctor

/-!
# Fppf descent for small étale sheaves

Fppf covering families of algebraic spaces satisfy descent for Type-valued
sheaves on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- For an fppf covering family of algebraic spaces over a scheme, the canonical
functor from Type-valued sheaves on the target's small étale site to descent data
along the family is an equivalence of categories. -/
@[stacks 0GFX, instance]
theorem descentIsEquivalenceOfFppfCovering
    {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) [FppfCovering Xᵢ f] :
    (pseudofunctor.toDescentData f).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
