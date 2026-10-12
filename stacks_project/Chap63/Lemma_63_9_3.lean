/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_9_3_Comparison
import StacksCheckRecall

/-!
# Associativity of derived étale lower shriek composition

Lemma 63.9.3: for separated finite-type morphisms of quasi-compact
quasi-separated schemes, the Lemma 63.9.2 composition identifications form a
commutative square `Rh_! ∘ Rg_! ∘ Rf_! ⇉ R(h ∘ g ∘ f)_!`.
-/

@[expose] public section

/- Lemma 63.9.3: Let `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ T` be separated
morphisms of finite type of quasi-compact and quasi-separated schemes. Then
the diagram of isomorphisms of Lemma 63.9.2 commutes. -/
@[stacks 0F7K]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.comp_assoc

end
