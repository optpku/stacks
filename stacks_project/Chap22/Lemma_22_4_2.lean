/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (J : Type w) [Category.{w} J]

/- Lemma 22.4.2 (09JJ) (1): right differential graded `A`-modules form an abelian category. -/
@[stacks 09JJ] #check
  (inferInstance : Abelian (DifferentialGradedModule.{u, w} A))

/- Lemma 22.4.2 (09JJ) (2): right differential graded `A`-modules have every limit shape
available in the base module category. -/
@[stacks 09JJ] #check
  (inferInstance : HasLimitsOfShape J (DifferentialGradedModule.{u, w} A))

/- Lemma 22.4.2 (09JJ) (3): right differential graded `A`-modules have every colimit shape
available in the base module category. -/
@[stacks 09JJ] #check
  (inferInstance : HasColimitsOfShape J (DifferentialGradedModule.{u, w} A))
