/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R]
variable {A E : CochainDGAlgebra.{u, v} R}
variable (φ : CochainDGAlgebra.Hom A E)

/- Lemma 22.26.9 (09LD): restriction of scalars along a cochain differential graded algebra
homomorphism is a differential graded functor on right differential graded modules. -/
@[stacks 09LD] #check
  (CochainDGAlgebra.Hom.restrictDgFunctor φ :
    DgFunctor R (DifferentialGradedModule.{u, w} E)
      (DifferentialGradedModule.{u, w} A))
#check @CochainDGAlgebra.Hom.restrictDgFunctor_map_apply
