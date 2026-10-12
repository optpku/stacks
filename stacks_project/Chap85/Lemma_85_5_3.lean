/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_5_3_Fiberwise
public import stacks_project.Chap85.Lemma_85_5_3_Total
import StacksCheckRecall

/-!
# Lemma 85.5.3

In the setup of Lemma 85.5.2, restriction along `g_n` commutes with unbounded
derived direct image of abelian sheaves: `(g'_n)⁻¹ ∘ R h_total,* K = R h_n,* ∘ g_n⁻¹ K`
for `K` in `D(Ab(C_total))`. The same identity holds in Situation 85.3.3 case A
(morphisms of sites) and case B (cocontinuous functors).
-/

@[expose] public section

open CategoryTheory

/- Lemma 85.5.3 (1)
In Situation 85.3.3 case A, with notation as in Lemma 85.5.2, for
`K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat)` one has
`(g'_n)⁻¹ (R h_total,* K) = R h_n,* (g_n⁻¹ K)` in `D(Ab(C'_n))`. -/
@[stacks 0D97] #check @SimplicialSites.IsMorphism.restrict_derivedPushforward

/- Lemma 85.5.3 (2)
In Situation 85.3.3 case B, with notation as in Lemma 85.5.2, for
`K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat)` one has
`(g'_n)⁻¹ (R h_total,* K) = R h_n,* (g_n⁻¹ K)` in `D(Ab(C'_n))`. -/
@[stacks 0D97] #check @Grothendieck.IsFiberwiseMorphism.restrict_derivedPushforward
