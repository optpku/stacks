module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.FittingIdeal

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 49.7.3: For a locally finite type morphism of schemes, the closed subscheme defined by
the Kähler different, represented by the zeroth Fitting ideal sheaf of its relative differentials,
has underlying support exactly the locus where the morphism is not unramified. -/
@[stacks 0BVY] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_support_eq_nonUnramifiedAtLocus :
    ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f],
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).support : Set Y) =
      {y : Y | ¬ f.UnramifiedAt y})
