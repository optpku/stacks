/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
import stacks_project.Chap66.Definition_66_4_1_Points
import stacks_project.Chap66.Definition_66_29_1_RingedSite
import stacks_project.Chap67.Definition_67_40_1_FiniteType
import stacks_project.Chap68.Lemma_68_17_4_Relative

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  [FiniteType f] [Decent f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
  (y : |Y|)

/- Situation 77.2.1: `S` is a scheme, `f : X ⟶ Y` is a finite type decent morphism
of algebraic spaces over `S`, `ℱ : X.Modules` is a finite type quasi-coherent
𝒪_X-module, and `y : |Y|` is a point of `Y`. -/
@[stacks 0CV6] #check (AlgebraicGeometry.AlgebraicSpace.Hom : ∀ {S : AlgebraicGeometry.Scheme.{u}},
  AlgebraicGeometry.AlgebraicSpace S → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
#check (f : AlgebraicGeometry.AlgebraicSpace.Hom X Y)
#check (inferInstance : AlgebraicGeometry.AlgebraicSpace.FiniteType f)
#check (inferInstance : AlgebraicGeometry.AlgebraicSpace.Decent f)
#check (ℱ : X.Modules)
#check (inferInstance : ℱ.IsQuasicoherent)
#check (inferInstance : ℱ.IsFiniteType)
#check (y : |Y|)

end
