/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Triangle
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A))
variable (sigma sigma' : DifferentialGradedModule.ShortComplex.GradedSplitting S)

/- Lemma 22.8.1 (09K6): the triangle attached to an admissible short exact sequence of
differential graded modules is independent, through the identity on all three vertices, of the
chosen graded `A`-linear splitting. -/
@[stacks 09K6]
#check (DifferentialGradedModule.ShortComplex.associatedTriangleIso S sigma sigma' :
  DifferentialGradedModule.ShortComplex.associatedTriangleK S sigma ≅
    DifferentialGradedModule.ShortComplex.associatedTriangleK S sigma')

/- The comparison is induced by the explicit graded `A`-linear splitting correction. -/
#check @DifferentialGradedModule.ShortComplex.splittingCorrection

/- That correction gives a concrete DG-module homotopy between the connecting maps. -/
#check @DifferentialGradedModule.ShortComplex.connectingHomotopy

/- Consequently, the two connecting maps agree in the intrinsic DG homotopy category. -/
#check @DifferentialGradedModule.ShortComplex.connectingHom_eq_in_K
