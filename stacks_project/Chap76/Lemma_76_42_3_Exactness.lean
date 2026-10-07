module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import stacks_project.Chap76.«76_42_2_1_Completion»

/-!
# Exactness of coherent completion on algebraic spaces

The canonical completion functor sending a coherent module `F` to the inverse
system of ideal-power quotients `n ↦ F / I ^ n F` is exact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

/-- The canonical completion functor `Coh(𝒪_X) ⥤ Coh(X, I)` is exact. -/
theorem exact {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    exactFunctor (Coh X) (CoherentFormalModules X I) (functor I) := sorry

/-- Canonical coherent completion preserves finite limits. -/
instance preservesFiniteLimits {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNoetherian X] (I : IdealSubobject X) [IsQuasiCoherent I] :
    PreservesFiniteLimits (functor I) := sorry

/-- Canonical coherent completion preserves finite colimits. -/
instance preservesFiniteColimits {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNoetherian X] (I : IdealSubobject X) [IsQuasiCoherent I] :
    PreservesFiniteColimits (functor I) := sorry

/-- Canonical coherent completion is additive. -/
instance additive {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] : (functor I).Additive := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
