/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : ChainComplex A ℤ} (f : K ⟶ L) (K : ChainComplex A ℤ)

/- Definition 12.13.4 (1) [010Z]: a quasi-isomorphism is a morphism inducing isomorphisms on
all homology objects. -/
@[stacks 010Z]
#check (QuasiIso f : Prop)

/- Definition 12.13.4 (2) [010Z]: a chain complex is acyclic when it is exact in every degree,
equivalently when all homology objects vanish. -/
@[stacks 010Z]
#check (K.Acyclic : Prop)

#check (quasiIso_iff f)
#check (HomologicalComplex.acyclic_iff K)
