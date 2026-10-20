/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {K L M : DifferentialGradedModule.{u, w} A}
variable (f : K ⟶ L) (g : L ⟶ M)
variable (S : ShortComplex (DifferentialGradedModule.{u, w} A))

/- Definition 22.7.1 (1) (09JT): a DG-module morphism is admissibly monic when its
underlying graded `A`-module morphism is split monic. -/
@[stacks 09JT] #check (IsAdmissibleMono f : Prop)

/- Definition 22.7.1 (2) (09JT): a DG-module morphism is admissibly epic when its
underlying graded `A`-module morphism is split epic. -/
@[stacks 09JT] #check (IsAdmissibleEpi g : Prop)

/- Definition 22.7.1 (3) (09JT): an admissible short exact sequence of DG-modules is short
exact and split after forgetting only the differential. -/
@[stacks 09JT] #check (IsAdmissibleShortExact S : Prop)

/- A chosen splitting retains graded `A`-linearity and is the construction-facing view. -/
#check (ShortComplex.GradedSplitting S : Type w)
