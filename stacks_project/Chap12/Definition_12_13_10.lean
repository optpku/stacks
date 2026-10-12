/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex A ℤ} (f : K ⟶ L) (K : CochainComplex A ℤ)

/- Definition 12.13.10 (1) [0115]: a quasi-isomorphism is a morphism inducing isomorphisms on
all cohomology objects. -/
@[stacks 0115]
#check (QuasiIso f : Prop)

/- Definition 12.13.10 (2) [0115]: a cochain complex is acyclic when it is exact in every
degree, equivalently when all cohomology objects vanish. -/
@[stacks 0115]
#check (K.Acyclic : Prop)

#check (quasiIso_iff f)
#check (HomologicalComplex.acyclic_iff K)
