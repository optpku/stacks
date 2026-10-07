module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.28.14 (0H79): for composable morphisms X ⟶ Y ⟶ S of ringed spaces, the canonical
sequence f^* Ω[Y/S] ⟶ Ω[X/S] ⟶ Ω[X/Y] ⟶ 0 is exact. -/
@[stacks 0H79]
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.exact

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.baseChange
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.baseChange_isComparison
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.baseChange_d
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.eq_baseChange
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.existsUnique_baseChange

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.projection

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.projectionDerivation

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.IsProjection

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.projection_d
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.projection_isProjection
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.eq_projection
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.existsUnique_projection

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.projection_epi

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.complex
