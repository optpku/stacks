/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksCheckRecall

@[expose] public section

/- Lemma 20.9.2: the degree-zero Čech comparison is bijective on every open cover exactly when
the abelian presheaf satisfies the canonical unique-gluing sheaf condition. -/
@[stacks 01EG "degree-zero Cech sheaf criterion"]
#check @TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
