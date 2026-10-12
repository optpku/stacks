/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap96.Lemma_96_9_3_Comparison
public import stacks_project.Chap96.Lemma_96_9_3_Restriction

/-!
# Lemma 96.9.3

Functoriality, étaleness, and inverse-image compatibility of the small-étale
comparison morphism `c_φ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/- Lemma 96.9.3 (1): If φ : x ⟶ y and ψ : y ⟶ z are morphisms of X lying over
a : U ⟶ V and b : V ⟶ W, then the composition a_small⁻¹(c_ψ) then c_φ equals
c_{ψ ∘ φ} via the identification (b ∘ a)_small⁻¹ = a_small⁻¹ ∘ b_small⁻¹. -/
@[stacks 075D]
#check comparison_comp

/- Lemma 96.9.3 (2): If φ : x ⟶ y lies over an étale morphism of schemes
a : U ⟶ V, then comparison φ F is an isomorphism. -/
@[stacks 075D]
#check comparison_isIso

/- Lemma 96.9.3 (3): If f : Y ⟶ X is a 1-morphism of categories fibred in
groupoids and y lies over U with image x = f(y), there is a canonical
identification f⁻¹ F|_{U_étale} = F|_{U_étale}. -/
@[stacks 075D]
#check restrictSmallEtaleSheaf_inverseImage

/- Lemma 96.9.3 (4): Given ψ : y' ⟶ y in Y lying over a : U' ⟶ U, the
comparison map c_ψ of f⁻¹ F equals the comparison map c_{f(ψ)} of F via the
identifications in (3). -/
@[stacks 075D]
#check comparison_inverseImage
