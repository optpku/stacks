module

public import stacks_project.Chap63.Lemma_63_9_2_Comparison
import StacksCheckRecall

/-!
# Composition of derived étale lower shriek

Lemma 63.9.2: for separated finite-type morphisms of quasi-compact
quasi-separated schemes, there is a canonical isomorphism
`Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` of compactification models.
-/

@[expose] public section

/- Lemma 63.9.2 (1): Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of
finite type of quasi-compact and quasi-separated schemes. There is a canonical
isomorphism `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` on objects of `D⁺_tors(X_étale, Λ)`. -/
@[stacks 0F7J]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.comp_isIso_of_isGE_isTorsion

/- Lemma 63.9.2 (2): Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of
finite type of quasi-compact and quasi-separated schemes. If `Λ` is a torsion
ring, then there is a canonical isomorphism `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` of
functors on `D(X_étale, Λ)`. -/
@[stacks 0F7J]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.comp_isIso_of_isTorsion

end
