module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.Radicial
import StacksCheckRecall

/-!
# Universally injective but not radicial

The structure morphism of `[Spec algebraicQ / Gal(algebraicQ / ℚ)]` over
`Spec ℚ` is universally injective, but not radicial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/- Example 76.3.3: the absolute Galois quotient over the rational spectrum is
universally injective but not radicial, with a nonempty reduced identity fibre. -/
@[stacks 0483] #check
  (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.not_radicial_toSpec :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{1}
        (pullback.diagonal toSpec).hom ∧
      ((MorphismProperty.over (@Etale)).relative uliftYoneda.{1} atlas.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) atlas.hom ∧
        AlgebraicGeometry.IsReduced cover.left) ∧
      Nonempty (sheafOfPoints.obj.obj (op cover)) ∧
      ∀ (L : Type) [Field L] [Algebra ℚ L] [IsPurelyInseparable ℚ L]
        (e : sheafOfPoints ≅
          (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
            (Over.mk (FieldExtension.specMap ℚ L))),
        e.hom ≫ (Scheme.fppfTopology.over base).uliftYoneda.{1}.map (specToBase L) ≠
          toSpec)
