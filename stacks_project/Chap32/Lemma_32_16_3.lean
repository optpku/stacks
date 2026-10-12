/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.DenseRange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 32.16.3: let `f : X ⟶ S` and `h : U ⟶ X` be finite-type morphisms of schemes, with
`S` locally Noetherian and `h` having dense range. If every DVR-valuative square over `f` whose
generic arrow factors through `h` admits a unique lift, then `f` is proper. -/
@[stacks 0CM5]
#check
  (AlgebraicGeometry.ValuativeCriterion.DVR.Along.isProper :
    ∀ {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X),
      [IsLocallyNoetherian S] → [Scheme.Hom.FiniteType f] → [Scheme.Hom.FiniteType h] →
        DenseRange h → ValuativeCriterion.DVR.Along.ExistsUnique h f → IsProper f)
