/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.Action.Basic

/-!
# Computations for the source-morphism evaluation action

Pointwise formulas for the strong transformations, modifications, and
hom-category functors induced by source morphisms.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Evaluation

/-- The component of the evaluation transformation induced by `f` is application of the
pseudofunctor's `1`-morphism map to `f`. -/
@[simp]
theorem evaluationMap.app
    {a b : B} (f : a ⟶ b) (F : Pseudofunctor B D) :
    (evaluationMap D f).app F = F.map f := sorry

/-- The naturality isomorphism of `evaluationMap f` is the inverse strong-naturality
isomorphism at `f`. -/
@[simp]
theorem evaluationMap.naturality
    {a b : B} (f : a ⟶ b) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    (evaluationMap D f).naturality η = (η.naturality f).symm := sorry

/-- The component of the evaluation modification induced by `γ` is application of the
pseudofunctor's `2`-morphism map to `γ`. -/
@[simp]
theorem evaluationMap₂.app
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g) (F : Pseudofunctor B D) :
    (evaluationMap₂ D γ).as.app F = F.map₂ γ := sorry

/-- The modification induced by a source `2`-morphism satisfies the pointwise
strong-naturality square.  This exposes its naturality without unfolding
`evaluationMap₂`. -/
@[reassoc]
theorem evaluationMap₂.naturality
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g)
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    η.app a ◁ G.map₂ γ ≫ (η.naturality g).inv =
      (η.naturality f).inv ≫ F.map₂ γ ▷ η.app b := sorry

/-- The object action of `evaluationMapFunctor` is the induced evaluation strong
transformation. -/
@[simp]
theorem evaluationMapFunctor.obj
    {a b : B} (f : a ⟶ b) :
    (evaluationMapFunctor D a b).obj f = evaluationMap D f := sorry

/-- The morphism action of `evaluationMapFunctor` is the induced evaluation modification. -/
@[simp]
theorem evaluationMapFunctor.map
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g) :
    (evaluationMapFunctor D a b).map γ = evaluationMap₂ D γ := sorry

end Evaluation

end Pseudofunctor

end CategoryTheory
