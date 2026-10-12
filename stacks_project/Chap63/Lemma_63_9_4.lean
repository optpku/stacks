/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_9_4_Cartesian
public import stacks_project.Chap63.Lemma_63_9_4_DerivedSites
public import stacks_project.Chap63.Lemma_63_9_4_LowerModel
public import stacks_project.Chap63.Lemma_63_9_4_SiteTransport
public import stacks_project.Chap63.Lemma_63_9_4_StackedComposition
public import stacks_project.Chap63.Lemma_63_9_4_StackedModels
public import stacks_project.Chap63.Lemma_63_9_4_StackedTransport
public import stacks_project.Chap63.Lemma_63_9_4_Transport
public import stacks_project.Chap63.Lemma_63_9_4_Comparison
import StacksCheckRecall

/-!
# Base change of derived étale lower shriek

Lemma 63.9.4: in a cartesian square of quasi-compact quasi-separated schemes
with `f` separated of finite type, there is a canonical isomorphism
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of compactification models, compatible with
the composition isomorphisms of Lemma 63.9.2.
-/

@[expose] public section

/- Lemma 63.9.4 (1): Consider a cartesian square of quasi-compact and
quasi-separated schemes with `f` separated and of finite type. Then there is a
canonical isomorphism `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` on objects of
`D⁺_tors(X_étale, Λ)`. -/
@[stacks 0F7L]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.baseChange_isIso_of_isGE_isTorsion

/- Lemma 63.9.4 (2): Consider a cartesian square of quasi-compact and
quasi-separated schemes with `f` separated and of finite type. If `Λ` is a
torsion ring, then there is a canonical isomorphism
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of functors on `D(X_étale, Λ)`. -/
@[stacks 0F7L]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.baseChange_isIso_of_isTorsion

/- Lemma 63.9.4 (3): Moreover, these isomorphisms are compatible with the
isomorphisms of Lemma 63.9.2. -/
@[stacks 0F7L]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.baseChange_comp

end
