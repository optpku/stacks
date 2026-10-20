module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.LimitPreserving
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 97.12.7
If `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
that is representable by algebraic spaces and locally of finite presentation,
then the forgetful 1-morphism `forgetToY F d : H_d(𝒳/𝒴) ⟶ 𝒴` is limit
preserving on objects. The source uses positive degree; the natural-degree
formulation also includes degree zero because finite locally free descent is
independent of the rank.
-/
@[stacks 06CH] #check
  (AlgebraicGeometry.FiniteHilbertStack.forgetToY.limitPreservingOnObjects :
    ∀ {S : Scheme.{u}}
      {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
      (F : 𝒳 ⟶ 𝒴) (d : ℕ)
      [Groupoids.Hom.LocallyOfFinitePresentation (StackOver.Groupoids.Hom.toGroupoidsMor F)],
      Groupoids.Hom.LimitPreservingOnObjects
        (StackOver.Groupoids.Hom.toGroupoidsMor
          (AlgebraicGeometry.FiniteHilbertStack.forgetToY F d)))
