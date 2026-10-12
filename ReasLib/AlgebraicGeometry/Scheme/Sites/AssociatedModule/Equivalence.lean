/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.FullyFaithful

/-!
# Equivalences induced by associated-module functors

The associated-module functors from quasi-coherent modules on a scheme to the
standard big and canonical small sites are equivalences.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor

/-- The associated-module functor to any of the five big standard sites is an equivalence. -/
instance isEquivalence (τ : StandardTopology) (S : Scheme.{u}) :
    (bigFunctor τ S).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor

namespace AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor

/-- The associated-module functor to a small Zariski or small étale site is an equivalence. -/
instance isEquivalence (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (smallFunctor σ S).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor
