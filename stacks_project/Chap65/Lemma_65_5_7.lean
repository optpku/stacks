/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 65.5.7: let `S` be a scheme and let `Fᵢ`, `Gᵢ` be presheaves of sets
`(Over S)ᵒᵖ ⥤ Type u` for `i = 1, 2`. Let `aᵢ : Fᵢ ⟶ Gᵢ` be representable
transformations of functors, and let `P` be a property of scheme morphisms in
the sense of Definition 65.5.1, stable under base change, fppf-local at the target,
and stable under composition. If `a₁` and
`a₂` have property `P`, then so does `a₁ × a₂ = prod.map a₁ a₂ : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂`. -/
@[stacks 02WM] #check (AlgebraicGeometry.Scheme.representableMorphismProperty.prod_map :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    [P.IsStableUnderComposition] {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u}
    (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂),
    Scheme.representableMorphismProperty S P a₁ →
    Scheme.representableMorphismProperty S P a₂ →
    Scheme.representableMorphismProperty S P (Limits.prod.map a₁ a₂))
