/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DifferentialGradedCategory R A] [DifferentialGradedCategory R B]
variable (F : DgFunctor R A B)

/- Lemma 22.26.5 (09L8): a differential graded functor induces functors on closed degree-zero
morphisms and on the corresponding homotopy categories. -/
@[stacks 09L8] #check (DgFunctor.mapComp F : Comp R A ⥤ Comp R B)
#check (DgFunctor.mapK F : K R A ⥤ K R B)
