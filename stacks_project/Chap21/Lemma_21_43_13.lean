/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.CounitHomEquiv.Leray
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.43.13 (0H0T): for a quasi-coherent `K` and arbitrary `M`, the local
topology-change adjunction, sections counit equivalence, and Leray comparison identify
`Hom(ε^* K, M)` with `Hom(RΓ(K), RΓ(M))`. -/
@[stacks 0H0T]
#check @Adjunction.CounitLeray.homEquiv

#check @Adjunction.CounitLeray.homEquiv_apply
#check @Adjunction.CounitLeray.homEquiv_symm_apply
