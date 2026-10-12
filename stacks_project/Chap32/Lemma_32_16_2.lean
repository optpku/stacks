/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.DenseRange
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 32.16.2: let `f : X ⟶ S` and `h : U ⟶ X` be morphisms of schemes. Assume that `S` is
locally Noetherian, that `f` is locally of finite type, that `h` is of finite type, and that
`h(U)` is dense in `X`. If every commutative DVR-valuative square whose generic arrow factors
through `h` admits at most one dotted arrow to `X`, then `f` is separated. -/
@[stacks 0CM4] #check (AlgebraicGeometry.ValuativeCriterion.DVR.Along.isSeparated :
  {U X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) → (h : U ⟶ X) →
    [AlgebraicGeometry.IsLocallyNoetherian S] →
    [AlgebraicGeometry.LocallyOfFiniteType f] →
    [AlgebraicGeometry.Scheme.Hom.FiniteType h] →
    DenseRange h →
    AlgebraicGeometry.ValuativeCriterion.DVR.Along.Uniqueness h f →
    AlgebraicGeometry.IsSeparated f)
