/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IntermediateField.GeneratorEmbedding
import StacksCheckRecall

@[expose] public section

/- Lemma 9.12.8 (Tag 09H7): evaluation of `F`-algebra homomorphisms on a spanning finite
generator tuple gives a bijection with tuples satisfying the successive transported-root
conditions. -/
#check FieldExtension.IsSuccessiveRootTuple
#check FieldExtension.adjoinStage_emb
@[stacks 09H7]
#check FieldExtension.algHom_successiveRootTuple_bijective
