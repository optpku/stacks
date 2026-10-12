/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap78.Lemma_78_12_3_QCoh
import stacks_project.Chap78.Lemma_78_12_3_Pullback
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H)

/- Lemma 78.12.3: a morphism `f : GroupoidAlgebraicSpace.Hom G H` of groupoids in algebraic
spaces over `B` induces the pullback functor `(F, α) ↦ (f^* F, f^* α)` from equivariant
quasi-coherent modules on `H` to equivariant quasi-coherent modules on `G`. -/
@[stacks 0442] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pullback f : H.QCoh ⥤ G.QCoh)

/- Companion checks: `GroupoidAlgebraicSpace.QCoh.pullback f` is built from the concrete object
and morphism formulas `GroupoidAlgebraicSpace.QCoh.pullbackObj f` and
`GroupoidAlgebraicSpace.QCoh.pullbackMap f`. -/
#check GroupoidAlgebraicSpace.QCoh.pullbackObj
#check GroupoidAlgebraicSpace.QCoh.pullbackMap
