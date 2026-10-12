/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_5_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_5_2_Total
import StacksCheckRecall

/-!
# Lemma 85.5.2

A morphism of simplicial sites in Situation 85.3.3 induces a morphism of topoi
of the total sites, commuting with the degree-`n` morphisms `g_n`, and satisfying
the mixed identity `(g'_n)⁻¹ ∘ h_total,* = h_n,* ∘ g_n⁻¹`.
-/

@[expose] public section

open CategoryTheory

/- Lemma 85.5.2 (1)
In Situation 85.3.3 case A, a morphism of simplicial sites induces a morphism of
topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by the continuous functor
`v_total = (Grothendieck.map (whiskerRight α Cat.opFunctor)).op`. -/
@[stacks 0D96] #check @SimplicialSites.IsMorphism.total

/- Lemma 85.5.2 (2)
The degree-`n` square commutes as morphisms of topoi:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
@[stacks 0D96] #check @SimplicialSites.IsMorphism.inverseImage_comp

/- Lemma 85.5.2 (3)
The mixed identity `(g'_n)⁻¹ ∘ h_total,* ≅ h_n,* ∘ g_n⁻¹` in case A. -/
@[stacks 0D96] #check @SimplicialSites.IsMorphism.restrict_pushforward

/- Lemma 85.5.2 (4)
In Situation 85.3.3 case B, a morphism of simplicial sites induces a morphism of
topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by the cocontinuous functor
`v_total = Grothendieck.map α`. -/
@[stacks 0D96] #check @Grothendieck.IsFiberwiseMorphism.total

/- Lemma 85.5.2 (5)
The degree-`n` square commutes as morphisms of topoi in case B:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
@[stacks 0D96] #check @Grothendieck.IsFiberwiseMorphism.inverseImage_comp

/- Lemma 85.5.2 (6)
The mixed identity `(g'_n)⁻¹ ∘ h_total,* ≅ h_n,* ∘ g_n⁻¹` in case B. -/
@[stacks 0D96] #check @Grothendieck.IsFiberwiseMorphism.restrict_pushforward
