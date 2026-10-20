module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.EnoughPoints
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 96.9.5: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
For `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the associated site `𝒳_τ`
has enough points. -/
@[stacks 06W4]
#check (AlgebraicGeometry.GroupoidsOver.hasEnoughPoints :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
      GrothendieckTopology.HasEnoughPoints.{u + 1} (X.associatedTopology τ))
