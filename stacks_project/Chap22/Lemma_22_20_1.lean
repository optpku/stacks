/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Telescope
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {P : DifferentialGradedModule.{u, v} A}
variable (F : DifferentialGradedModule.PropertyP.Filtration A P)

/- Lemma 22.20.1 (09KL): the telescope sequence associated to a property P filtration is
admissibly short exact. -/
@[stacks 09KL] #check
  (F.telescopeIsAdmissibleShortExact :
    DifferentialGradedModule.IsAdmissibleShortExact F.telescopeShortComplex)
