module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.InternalHom.Triangulated

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Pretriangulated.Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} (K L : ModuleDerived X)

/- Lemma 20.42.4 (08I0): the actual derived sheaf internal-Hom bifunctor transforms
 distinguished triangles into distinguished triangles in its covariant target variable. -/
@[stacks 08I0 "actual target-variable distinguished triangles"]
#check (inferInstance : (ModuleDerived.InternalHom.targetFunctor X K).IsTriangulated)

/- Lemma 20.42.4 (08I0): the actual derived sheaf internal-Hom bifunctor transforms
 distinguished triangles into distinguished triangles in its contravariant source variable. -/
@[stacks 08I0 "actual source-variable distinguished triangles"]
#check (inferInstance : (ModuleDerived.InternalHom.sourceFunctor X L).IsTriangulated)

/- Canonical generic infrastructure remains available to the chapter's import clients. -/
#check @MonoidalClosed.ihom_commShift_of_tensorLeft
#check @MonoidalClosed.ihom_isTriangulated_of_tensorLeft
#check @MonoidalClosed.internalHomFlip_commShift_of_tensorRight
#check @MonoidalClosed.internalHomFlip_isTriangulated_of_tensorRight

end AlgebraicGeometry.RingedSpace

end
