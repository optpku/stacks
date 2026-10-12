/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RegularLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.25.8 (1): over a perfect field, the smooth locus of a reduced locally algebraic
scheme is its regular locus. -/
@[stacks 0B8X] #check
  (AlgebraicGeometry.SchemeOverField.RegularLocus.smoothAt_set_eq :
    ∀ {k : Type u} [Field k] [PerfectField k]
      (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left],
      { x : X.left | X.hom.SmoothAt x } = Reg(X.left))

/- Lemma 33.25.8 (2): the regular locus of a reduced locally algebraic scheme over a perfect
field is open. -/
@[stacks 0B8X] #check
  (AlgebraicGeometry.SchemeOverField.RegularLocus.isOpen :
    ∀ {k : Type u} [Field k] [PerfectField k]
      (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left],
      IsOpen (Reg(X.left) : Set X.left))

/- Lemma 33.25.8 (3): the regular locus of a reduced locally algebraic scheme over a perfect
field is dense. -/
@[stacks 0B8X] #check
  (AlgebraicGeometry.SchemeOverField.RegularLocus.dense :
    ∀ {k : Type u} [Field k] [PerfectField k]
      (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left],
      Dense (Reg(X.left) : Set X.left))
