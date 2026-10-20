module

public import stacks_project.Chap59.Lemma_59_48_5
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 59.48.6 (1): for a closed immersion `f : X ⟶ Y` and
`τ ∈ {syntomic, smooth, etale}`, the big-site pushforward preserves
coequalizers. -/
@[stacks 04C4] #check
  (AlgebraicGeometry.StandardTopology.Big.pushforward_preserves_coequalizers_of_closedImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (τ : StandardTopology),
      (τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) →
        PreservesColimitsOfShape WalkingParallelPair
          ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
            (τ.overTopology Y) (τ.overTopology X)))

/- Lemma 59.48.6 (2): for a closed immersion `f : X ⟶ Y` and
`τ ∈ {syntomic, smooth, etale}`, the big-site pushforward preserves
pushouts. -/
@[stacks 04C4] #check
  (AlgebraicGeometry.StandardTopology.Big.pushforward_preserves_pushouts_of_closedImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (τ : StandardTopology),
      (τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) →
        PreservesColimitsOfShape WalkingSpan
          ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
            (τ.overTopology Y) (τ.overTopology X)))

/- Lemma 59.48.6 (3): for a closed immersion `f : X ⟶ Y` and
`τ ∈ {syntomic, smooth, etale}`, the big-site pushforward on abelian
sheaves is exact. -/
@[stacks 04C4] #check
  (AlgebraicGeometry.StandardTopology.Big.pushforward_exact_on_abelian_sheaves_of_closedImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (τ : StandardTopology),
      (τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) →
        exactFunctor
          (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})
          (Sheaf (τ.overTopology Y) AddCommGrpCat.{u + 1})
          ((Over.pullback f).sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
            (τ.overTopology Y) (τ.overTopology X)))
