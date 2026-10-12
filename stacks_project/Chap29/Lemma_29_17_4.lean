/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.IrreducibleComponent
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.17.4: a locally Noetherian scheme is universally catenary if and only if each of its
irreducible components, with its reduced induced closed-subscheme structure, is universally
catenary. -/
@[stacks 0G42] #check
  (AlgebraicGeometry.universallyCatenary_iff_forall_irreducibleComponent :
    ∀ (S : Scheme.{u}) [IsLocallyNoetherian S],
      UniversallyCatenary S ↔
        ∀ Z : irreducibleComponents S,
          UniversallyCatenary (S.irreducibleComponentSubscheme Z))
