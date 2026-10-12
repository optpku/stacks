/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek
import StacksCheckRecall

@[expose] public section

/- Definition 63.3.3: if `f : X ⟶ Y` is a separated, locally of finite type
morphism of schemes and `F` is an abelian sheaf on `X_étale`, the Lemma 63.3.1
subsheaf of `f_* F` consisting of sections whose étale support is proper over
the base is named `etaleLowerShriek f`, the direct image with compact support.
The inclusion `etaleLowerShriekι` realizes
`etaleLowerShriek f ⟶ etaleAbelianPushforward f`. -/
@[stacks 0F4Z] #check AlgebraicGeometry.Scheme.Etale.etaleLowerShriek

end
