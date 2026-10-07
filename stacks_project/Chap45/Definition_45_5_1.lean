module

public import ReasLib.AlgebraicGeometry.ChowMotive.ChowGroup
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u x

/- Definition 45.5.1: for a Chow motive `M = (X, p, m)` over `k`, the `i`th Chow
group is the image of `p` under the degree-`i` realization. -/
@[stacks 0FGL] #check
  (ChowMotive.chowGroup :
    ∀ {k : Type u} [Field k]
      {GradedCorrespondence : Type u → Type v}
      [Category.{w} (GradedCorrespondence k)],
      (ℤ → GradedCorrespondence k ⥤ ModuleCat.{x} ℚ) →
        ChowMotive k GradedCorrespondence → ℤ → ModuleCat.{x} ℚ)
