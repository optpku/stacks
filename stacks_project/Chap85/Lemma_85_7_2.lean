module

public import stacks_project.Chap85.Lemma_85_7_2_Component
public import stacks_project.Chap85.Lemma_85_7_2_Fiberwise
import StacksCheckRecall

/-!
# Lemma 85.7.2

A morphism of ringed simplicial sites in Situation 85.3.3 induces a morphism of
ringed topoi of the total sites, commuting with the degree-`n` morphisms `g_n`
of Lemma 85.6.1, and satisfying the mixed identity
`(g'_n)* ∘ h_total,* = h_n,* ∘ g_n^*` on modules.
-/

@[expose] public section

open CategoryTheory

/- Lemma 85.7.2 (1)
In Situation 85.3.3 case A, a morphism of ringed simplicial sites induces a
morphism of ringed topoi `h_total : (Sh(C_total), O) ⟶ (Sh(C'_total), O')`. -/
@[stacks 0DH0] #check @SimplicialSites.RingedMorphism.toToposHom

/- Lemma 85.7.2 (2)
The degree-`n` square commutes as morphisms of ringed topoi:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`, with `g_n` and `g'_n` as in
Lemma 85.6.1. -/
@[stacks 0DH0] #check @SimplicialSites.RingedMorphism.inverseImage_comp

/- Lemma 85.7.2 (3)
The mixed identity `(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` as functors
`Mod(O) ⥤ Mod(O'_n)` in case A. -/
@[stacks 0DH0] #check @SimplicialSites.RingedMorphism.restrict_modulePushforward

/- Lemma 85.7.2 (4)
In Situation 85.3.3 case B, a morphism of ringed simplicial sites induces a
morphism of ringed topoi `h_total : (Sh(C_total), O) ⟶ (Sh(C'_total), O')`. -/
@[stacks 0DH0] #check @Grothendieck.RingedMorphism.toToposHom

/- Lemma 85.7.2 (5)
The degree-`n` square commutes as morphisms of ringed topoi in case B:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
@[stacks 0DH0] #check @Grothendieck.RingedMorphism.inverseImage_comp

/- Lemma 85.7.2 (6)
The mixed identity `(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` as functors
`Mod(O) ⥤ Mod(O'_n)` in case B. -/
@[stacks 0DH0] #check @Grothendieck.RingedMorphism.restrict_modulePushforward
