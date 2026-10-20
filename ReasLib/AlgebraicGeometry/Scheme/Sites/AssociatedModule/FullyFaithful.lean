/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Functor

/-!
# Full faithfulness of associated-module functors

The associated-module functors from quasi-coherent modules on a scheme to the
standard big and canonical small sites are fully faithful.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor

/-- The associated-module functor to any of the five big standard sites is fully faithful. -/
theorem fullyFaithful (τ : StandardTopology) (S : Scheme.{u}) :
    Nonempty (bigFunctor τ S).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor

namespace AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor

/-- The associated-module functor to a small Zariski or small étale site is fully faithful. -/
theorem fullyFaithful (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Nonempty (smallFunctor σ S).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor
