module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import stacks_project.Chap99.Situation_99_5_1

/-!
# Lemma 99.5.2

In Situation 99.5.1 the functor `p : CohStack f ⟶ Over S` is fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.5.2: in Situation 99.5.1, with `f : X ⟶ B` of finite presentation,
the projection `p : CohStack f ⟶ Over S`, `(T, g, F) ↦ T`, is fibred in groupoids. -/
@[stacks 08W5]
instance instIsFiberedInGroupoids (f : X ⟶ B) [FinitePresentation f] :
    Functor.IsFibered.InGroupoids (p f) := sorry

/-- The category of finitely presented quasi-coherent modules with proper
support on the fibres of `f`, bundled as a category fibred in groupoids over
`Over S`. The Hom-universe is `u + 1`, so this cannot land in `GroupoidsOver S`. -/
def toGroupoids (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f)

/-- The projection of `toGroupoids f` is the source functor `p f`, sending
`(T, g, F)` to `T`. -/
theorem toGroupoids_p (f : X ⟶ B) [FinitePresentation f] :
    (toGroupoids f).p = p f := sorry

/-- The total category of `toGroupoids f` is the category `Obj f` of
Situation 99.5.1. -/
theorem toGroupoids_total (f : X ⟶ B) [FinitePresentation f] :
    (toGroupoids f).total = Obj f := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack

