/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.PuncturedAffineSpace.Factorization

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 32.9.2: a canonical chart of countably generated affine space with doubled origin
cannot factor as a closed immersion followed by a morphism of finite presentation. -/
@[stacks 01ZF] #check
  (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.countableChartMap_not_closedImmersion_finitePresentation_factorization :
    ∀ (k : Type u) [Field k] (j : Fin 2),
      ¬ (MorphismProperty.comp @IsClosedImmersion
        (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme))
        (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.chartMap (ULift.{u} ℕ) k j))

/- Closed-immersion and finite-presentation factorizations are quasi-compact. -/
#check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.closedImmersion_comp_le_quasiCompact :
    (MorphismProperty.comp @IsClosedImmersion
      (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme)) ≤ @QuasiCompact)

/- Every canonical chart of an infinite-dimensional doubled punctured affine space is not
quasi-compact. -/
#check
  (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.chartMap_not_quasiCompact :
    ∀ (ι : Type u) [Infinite ι] (k : Type u) [CommRing k] [Nontrivial k] (j : Fin 2),
      ¬ QuasiCompact
        (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.chartMap ι k j))
