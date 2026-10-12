/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_7_3_Component
public import stacks_project.Chap85.Lemma_85_7_3_Fiberwise
import StacksCheckRecall

/-!
# Lemma 85.7.3

With notation and hypotheses as in Lemma 85.7.2, for `K` in `D(O)` one has
`(g'_n)^* (R h_total,* K) = R h_n,* (g_n^* K)` in `D(O'_n)`. The same identity
holds in Situation 85.3.3 case A and case B.
-/

@[expose] public section

open CategoryTheory

/- Lemma 85.7.3 (1)
In Situation 85.3.3 case A, with notation as in Lemma 85.7.2, for
`K : ModuleDerived (Sh(C_total), O)` one has
`(g'_n)^* (R h_total,* K) = R h_n,* (g_n^* K)` in `D(O'_n)`. -/
@[stacks 0DH1] #check @SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_hom_isIso

@[stacks 0DH1] #check @SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_hom
#check @SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_obj_isIso

/- Lemma 85.7.3 (2)
In Situation 85.3.3 case B, with notation as in Lemma 85.7.2, for
`K : ModuleDerived (Sh(C_total), O)` one has
`(g'_n)^* (R h_total,* K) = R h_n,* (g_n^* K)` in `D(O'_n)`. -/
@[stacks 0DH1] #check @Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_hom_isIso

@[stacks 0DH1] #check @Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_hom
#check @Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_obj_isIso
