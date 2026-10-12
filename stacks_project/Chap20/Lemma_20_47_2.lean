/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.2 (1) (08CC): recall the representative characterization of derived
`m`-pseudo-coherence. -/
@[stacks 08CC "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isMPseudoCoherent_iff_exists_mPseudoCoherent_representative

/- Lemma 20.47.2 (2) (08CC): every chosen representative of an `m`-pseudo-coherent derived
module is `m`-pseudo-coherent. -/
@[stacks 08CC "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.of_representation

-- The construction in the opposite direction is independently reusable.
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsMPseudoCoherent.q_obj
