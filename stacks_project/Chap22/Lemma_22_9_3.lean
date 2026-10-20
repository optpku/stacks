/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
variable (phi :
  DifferentialGradedModule.MappingCone.triangleK f₁ ⟶
    DifferentialGradedModule.MappingCone.triangleK f₂)
variable [IsIso phi.hom₁] [IsIso phi.hom₂]

/- Lemma 22.9.3 (09KE): a morphism between the standard mapping-cone triangles of right
differential graded `A`-modules is an isomorphism on the cone whenever it is an isomorphism on
the source and target. -/
@[stacks 09KE]
#check (DifferentialGradedModule.MappingCone.triangleK_isIso₃_of_isIso₁₂ phi :
  IsIso phi.hom₃)
