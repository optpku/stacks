/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (T : DifferentialGradedBimodule A B)

/- Lemma 22.31.1 (09LH): the actual fixed-source internal-Hom functor on DG homotopy
categories is triangulated. -/
@[stacks 09LH]
#check (inferInstance :
  (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.IsTriangulated)

/- Its shift compatibility is the global instance built from the sign-free comparison. -/
#check (inferInstance :
  (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.CommShift ℤ)

/- The reusable comparison itself remains available without instance search. -/
#check DifferentialGradedBimodule.InternalHom.mapKCommShiftIso T
