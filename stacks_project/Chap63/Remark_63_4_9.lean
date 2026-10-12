/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_4_9_Pushforward
public import stacks_project.Chap63.Remark_63_4_9_Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Remark 63.4.9 (1): for a scheme morphism `g : Y' ⟶ Y` and an abelian presheaf
`G'` on `Y'_étale`, the pushforward `g_* G'` is the presheaf
`V ↦ G'((smallEtalePullback g).obj V)` on `Y_étale`. -/
@[stacks 0F78]
#check presheafPushforwardAb

/- Remark 63.4.9 (2): a map `α : G ⟶ g_* G'` of abelian presheaves on `Y_étale`
induces a unique map `α^# : G^# ⟶ g_* ((G')^#)` of abelian sheaves making the
sheafification-unit square commute. -/
@[stacks 0F78]
#check sheafifyPresheafPushforward

/- Remark 63.4.9 (3): the map `α' : g⁻¹ G^# ⟶ (G')^#` is the adjunct of `α^#`. -/
@[stacks 0F78]
#check sheafifyPresheafPushforwardAdjoint

/- Remark 63.4.9 (4): for a geometric point `ȳ'` of `Y'` with image `ȳ = g ∘ ȳ'`,
the stalk map `α'_ȳ'` sends the germ of a section `s` of `G` over an étale
neighbourhood `(V, v̄)` of `ȳ` to the germ of `α(s)` over the étale neighbourhood
`(pullbackNeighborhood g ȳ' (V, v̄))` of `ȳ'`. -/
@[stacks 0F78]
#check sheafifyPresheafPushforwardAdjoint_stalk

end
