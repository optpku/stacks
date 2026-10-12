/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.AlmostCocontinuous
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Colimits
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Big-site pushforward along a closed immersion preserves coequalizers of
sheaves of sets for the syntomic, smooth, and étale topologies. -/
theorem pushforward_preserves_coequalizers_of_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (τ : StandardTopology)
    (hτ : τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) :
    PreservesColimitsOfShape WalkingParallelPair
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (τ.overTopology Y) (τ.overTopology X)) := sorry

/-- Big-site pushforward along a closed immersion preserves pushouts of
sheaves of sets for the syntomic, smooth, and étale topologies. -/
theorem pushforward_preserves_pushouts_of_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (τ : StandardTopology)
    (hτ : τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) :
    PreservesColimitsOfShape WalkingSpan
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (τ.overTopology Y) (τ.overTopology X)) := sorry

/-- Big-site pushforward along a closed immersion is exact on sheaves of
abelian groups for the syntomic, smooth, and étale topologies. -/
theorem pushforward_exact_on_abelian_sheaves_of_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (τ : StandardTopology)
    (hτ : τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) :
    exactFunctor
      (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})
      (Sheaf (τ.overTopology Y) AddCommGrpCat.{u + 1})
      ((Over.pullback f).sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
        (τ.overTopology Y) (τ.overTopology X)) := sorry

end AlgebraicGeometry.StandardTopology.Big
