/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
variable (i : Z ⟶ X) [IsClosedImmersion i]

/- Lemma 30.9.8: Pushforward along a closed immersion of locally Noetherian schemes induces an
equivalence from coherent modules on the closed subscheme to coherent modules on the ambient
scheme annihilated by the kernel ideal cutting out the closed subscheme. -/
@[stacks 087T] #check
  (AlgebraicGeometry.Scheme.Modules.ClosedImmersion.coherentPushforward_isEquivalence i :
    (AlgebraicGeometry.Scheme.Modules.ClosedImmersion.coherentPushforward i).IsEquivalence)
