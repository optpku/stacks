/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of simplicial copowers in the object variable

A fixed simplicial set acts on simplicial objects by copower. This file owns the induced
components, morphisms, and endofunctor in the simplicial-object variable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section ObjectVariable

variable (U : SSet.{w})
variable {W W' : SimplicialObject C}

/-- The raw component of the copower morphism induced by a morphism in the
simplicial-object variable. -/
@[stacks 017E "copower induced component"]
abbrev copower.homApp
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') (Δ : SimplexCategoryᵒᵖ) :
    (copower U W).obj Δ ⟶ (copower U W').obj Δ :=
  Functor.indexedCoprod.homApp U f Δ

/-- The raw components induced by a simplicial-object morphism form a natural family. -/
@[stacks 017E "copower induced naturality"]
theorem copower.homApp.naturality
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (copower U W).map σ ≫ copower.homApp U f Δ₂ =
      copower.homApp U f Δ₁ ≫ (copower U W').map σ := sorry

/-- The morphism of simplicial copowers induced by a morphism `f : W ⟶ W'` in the
simplicial-object variable. Degreewise, it maps each summand by `f.app Δ`. -/
@[stacks 017E "copower morphism in the object variable"]
abbrev copower.hom
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') :
    copower U W ⟶ copower U W' :=
  Functor.indexedCoprod.hom U f

/-- The component of `copower.hom` is its corresponding raw component. -/
@[simp, stacks 017E "copower induced component formula"]
theorem copower.hom_app
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') (Δ : SimplexCategoryᵒᵖ) :
    (copower.hom U f).app Δ = copower.homApp U f Δ := sorry

/-- Computing `copower.hom` after a coproduct injection. -/
@[simp, stacks 017E "copower induced injection formula"]
theorem copower.hom.ι
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    Sigma.ι (fun _ : U.obj Δ ↦ W.obj Δ) u ≫ (copower.hom U f).app Δ =
      f.app Δ ≫ Sigma.ι (fun _ : U.obj Δ ↦ W'.obj Δ) u := sorry

/-- Identity law for `copower.hom`. -/
@[simp, stacks 017E "copower induced identity"]
theorem copower.hom.id
    (W : SimplicialObject C)
    [HasCopower U W] :
    copower.hom U (𝟙 W) = 𝟙 (copower U W) := sorry

/-- Composition law for `copower.hom`. -/
@[stacks 017E "copower induced composition"]
theorem copower.hom.comp
    {W₁ W₂ W₃ : SimplicialObject C}
    [HasCopower U W₁] [HasCopower U W₂] [HasCopower U W₃]
    (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) :
    copower.hom U (f ≫ g) = copower.hom U f ≫ copower.hom U g := sorry

end ObjectVariable

section ObjectVariableFunctor

variable (U : SSet.{w})
variable [HasCopowers U C]

/-- The functor `X ↦ copower U X` in the simplicial-object variable. -/
@[stacks 017E "copower functor in the object variable"]
abbrev copower.functor : SimplicialObject C ⥤ SimplicialObject C :=
  Functor.indexedCoprod.functor U

end ObjectVariableFunctor

end CategoryTheory.SimplicialObject
