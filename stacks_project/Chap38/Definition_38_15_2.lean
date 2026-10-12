/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity
import StacksCheckRecall
import stacks_project.Chap38.Situation_38_15_1
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory AlgebraicGeometry

universe u

section

variable {S X : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
variable (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S)

/- Definition 38.15.2: an impurity of `F` above `s` consists of a base change,
a specialization over `s`, and a relative associated point whose closure misses the
special fibre. -/
@[stacks 05IY] #check (AlgebraicGeometry.Scheme.Modules.Impurity F f s : Type (u + 1))

end
