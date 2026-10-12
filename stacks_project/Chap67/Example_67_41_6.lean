/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Example_67_41_6_Fold
public import stacks_project.Chap67.Example_67_41_6_ValuativeSquare
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

universe u

/- Example 67.41.6 (1): Lemma 67.8.8 atlas test for the structure morphism
`π : X ⟶ 𝔸¹_k`. The base-change projection of `π` along the étale-surjective
cover `U ⟶ 𝔸¹_k` is representably quasi-compact; see `etale_cover_hom` and
`surjective_cover_hom` for the atlas leg. -/
@[stacks 03KI] #check quasiCompact_structureHom

/- Example 67.41.6 (2): Lemma 67.9.5 atlas test for the structure morphism
`π : X ⟶ 𝔸¹_k`. The base-change projection of `π` along the étale-surjective
cover `U ⟶ 𝔸¹_k` is representably universally closed; see `etale_cover_hom` and
`surjective_cover_hom` for the atlas leg. -/
@[stacks 03KI] #check universallyClosed_structureHom

/- Example 67.41.6 (3): the valuative square `Spec(k⸨X⸩) ⟶ X` over
`Spec(k⟦X⟧) ⟶ 𝔸¹_k` has no dotted lift. -/
@[stacks 03KI] #check not_hasLift

/- After base change along `U ⟶ 𝔸¹_k`, `π` is identified with the doubled-origin fold. -/
#check iso_doubledOrigin
#check structureHomPullback_iso
#check doubledOriginToCover_left
#check etale_cover_hom
#check surjective_cover_hom
#check fiber_origin_iso
