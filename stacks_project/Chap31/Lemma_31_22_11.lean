/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Syntomic
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.22.11: in a commutative triangle `Y -i-> X -f-> S` and `Y -p-> S`,
if `p` and `f` are smooth and `i` is an immersion, then `i` is a regular immersion. -/
@[stacks 067U] #check
  (AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth_of_isImmersion :
    ∀ {Y X S : Scheme.{u}} (i : Y ⟶ X) (p : Y ⟶ S) (f : X ⟶ S) [IsImmersion i],
      i ≫ f = p → Smooth p → Smooth f → IsRegularImmersion i)
