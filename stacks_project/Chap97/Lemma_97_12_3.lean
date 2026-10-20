/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Etale
import StacksCheckRecall

/-!
# Lemma 97.12.3

In the identity-base specialization of Lemma 97.12.1, an étale (optionally
surjective) 1-morphism `G` induces an étale (optionally surjective) 1-morphism
of finite Hilbert stacks of positive degree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

universe u

/- Lemma 97.12.3 (1): in the situation of Lemma 97.12.1 with `𝒴' = 𝒴` and
`H = 𝟙 𝒴`, if `G` is representable by algebraic spaces and étale, then the
induced 1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic
spaces and étale. -/
@[stacks 05YG] #check
  (AlgebraicGeometry.finiteHilbertMapSquare.etale :
    ∀ {S : Scheme.{u}} {𝒳' 𝒳 𝒴 :
      StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
      (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
      (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ) [NeZero d]
      [Groupoids.Hom.Etale (asGroupoidsOverMor G)],
      Groupoids.Hom.Etale
        (asGroupoidsOverMor (finiteHilbertMapSquare F' F G (𝟙 𝒴) γ d)))

/- Lemma 97.12.3 (2): in the same situation, if `G` is also surjective, then
the induced 1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is surjective. -/
@[stacks 05YG] #check
  (AlgebraicGeometry.finiteHilbertMapSquare.surjective :
    ∀ {S : Scheme.{u}} {𝒳' 𝒳 𝒴 :
      StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
      (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
      (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ) [NeZero d]
      [Groupoids.Hom.Etale (asGroupoidsOverMor G)]
      [Groupoids.Hom.Surjective (asGroupoidsOverMor G)],
      Groupoids.Hom.Surjective
        (asGroupoidsOverMor (finiteHilbertMapSquare F' F G (𝟙 𝒴) γ d)))
