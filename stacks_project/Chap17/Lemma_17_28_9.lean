/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
import StacksCheckRecall

@[expose] public section

/-!
Lemma 17.28.9 (08TF): for a surjective morphism in a tower of commutative-ring sheaves, the
conormal sequence
`I / I ^ 2 ⟶ O₃ ⊗[O₂] Ω(O₂/O₁) ⟶ Ω(O₃/O₁) ⟶ 0`
is exact, and its left map sends a cotangent class represented by `x` to `1 ⊗ d x`.

The reusable owner is formulated on an arbitrary site.  Surjectivity is represented by
`Sheaf.IsLocallySurjective`, which specializes to surjectivity on stalks for sheaves on a
topological space.
-/

/- Lemma 17.28.9 (08TF) (1): exactness at the base-changed differentials. -/
@[stacks 08TF "(1)"]
#check @SheafOfModules.RingedSite.conormalSequence_exact

/- Lemma 17.28.9 (08TF) (2): exactness at the final zero term. -/
@[stacks 08TF "(2)"]
#check @SheafOfModules.RingedSite.conormalToDifferentials_epi

/- Lemma 17.28.9 (08TF) (3): the left map is `x ↦ 1 ⊗ d x` on generators. -/
@[stacks 08TF "(3)"]
#check @SheafOfModules.RingedSite.sectionConormalMap_toCotangent

#check @SheafOfModules.RingedSite.conormalSource
#check @SheafOfModules.RingedSite.conormalTensorTerm
#check @SheafOfModules.RingedSite.conormalMap
#check @SheafOfModules.RingedSite.conormalToDifferentials
#check @KaehlerDifferential.kerCotangentToTensor_toCotangent
