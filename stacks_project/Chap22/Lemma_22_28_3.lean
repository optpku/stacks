/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Enveloping
import StacksCheckRecall

@[expose] public section

universe u v w x

open CategoryTheory

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R)

/- Lemma 22.28.3 (0FQJ): DG `(A, B)`-bimodules are canonically equivalent to right DG modules
over `A.opposite ⊗[R] B`. -/
@[stacks 0FQJ] #check
  (DifferentialGradedBimodule.envelopingEquivalence A B :
    DifferentialGradedBimodule A B ≌
      DifferentialGradedModule (CochainDGAlgebra.enveloping A B))

#check @CochainDGAlgebra.Enveloping.leftHom
#check @CochainDGAlgebra.Enveloping.rightHom
