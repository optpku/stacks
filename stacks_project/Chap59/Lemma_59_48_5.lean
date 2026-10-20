module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.AlmostCocontinuous
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 59.48.5: for a closed immersion `f : X ⟶ Y` and
`τ ∈ {syntomic, smooth, étale}`, the pullback functor
`Over.pullback f` is almost cocontinuous from the big
`τ`-site over `Y` to the big `τ`-site over `X`. -/
@[stacks 04C3] #check
  (AlgebraicGeometry.StandardTopology.Big.pullback_isAlmostCocontinuous_of_closedImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (τ : StandardTopology),
      (τ = .syntomic ∨ τ = .smooth ∨ τ = .etale) →
        Functor.IsAlmostCocontinuous (Over.pullback f)
          (τ.overTopology Y) (τ.overTopology X))
