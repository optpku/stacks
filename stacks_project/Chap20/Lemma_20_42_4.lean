module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped Pretriangulated.Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]

/-
Lemma 20.42.4 (08I0): the derived internal-Hom bifunctor sends distinguished triangles to
distinguished triangles in each variable.  The reusable owner states the exact categorical
boundary: exactness in either internal-Hom variable follows from exactness of the corresponding
fixed-factor tensor functor.
-/

section Target

variable (K : ModuleDerived X)
variable [(tensorLeft K).CommShift ℤ] [(tensorLeft K).IsTriangulated]

@[stacks 08I0 "Lemma 20.42.4, target-variable distinguished triangles"]
#check (inferInstance : (ihom K).IsTriangulated)

#check @ihom_commShift_of_tensorLeft
#check @ihom_isTriangulated_of_tensorLeft

end Target

section Source

variable (L : ModuleDerived X)
variable [((tensoringRight (ModuleDerived X)).obj L).CommShift ℤ]
variable [((tensoringRight (ModuleDerived X)).obj L).IsTriangulated]

@[stacks 08I0 "Lemma 20.42.4, source-variable distinguished triangles"]
#check (inferInstance :
  ((MonoidalClosed.internalHom (C := ModuleDerived X)).flip.obj L).IsTriangulated)

#check @internalHomFlip_commShift_of_tensorRight
#check @internalHomFlip_isTriangulated_of_tensorRight

end Source

end AlgebraicGeometry.RingedSpace

end
