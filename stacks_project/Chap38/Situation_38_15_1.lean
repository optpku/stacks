module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory AlgebraicGeometry

universe u

section

variable {S X : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)

/- Situation 38.15.1: `S` and `X` are schemes, `f : X ⟶ S` is of finite type,
`ℱ : X.Modules` is finite type and quasicoherent, and `s : S` is a point of `S`. -/
@[stacks 05FW] #check (AlgebraicGeometry.Scheme.Hom.FiniteType f : Prop)

#check (inferInstance : AlgebraicGeometry.Scheme.Hom.FiniteType f)
#check (f : X ⟶ S)
#check (ℱ : X.Modules)
#check (inferInstance : ℱ.IsQuasicoherent)
#check (inferInstance : ℱ.IsFiniteType)
#check (s : S)

end
