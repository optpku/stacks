/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Computations.Action

/-!
# Naturality of the explicit pseudo-pullback pseudofunctor

This focused leaf owns naturality and extensionality for the bundled `2`-cell action. Pointwise
component and verticality formulas remain in `Computations.Action`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped Bicategory

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The bundled pseudo-pullback `2`-cell action is natural in source pseudo-pullback morphisms. -/
@[reassoc]
theorem pseudofunctor.map₂.naturality
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ)
    {P Q : (PseudoPullback S.fst S.snd).obj} (χ : P ⟶ Q) :
    ((pseudofunctor C).map ψ).toFunctor.map χ ≫
        ((pseudofunctor C).map₂ Γ).toNatTrans.app Q =
      ((pseudofunctor C).map₂ Γ).toNatTrans.app P ≫
        ((pseudofunctor C).map φ).toFunctor.map χ := sorry

/-- Packaged pseudo-pullback `2`-cells are determined by their objectwise components. -/
theorem pseudofunctor.map₂.ext
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} {Γ Δ : ψ ⟶ φ}
    (h : ∀ P : (PseudoPullback S.fst S.snd).obj,
      ((pseudofunctor C).map₂ Γ).toNatTrans.app P =
        ((pseudofunctor C).map₂ Δ).toNatTrans.app P) :
    (pseudofunctor C).map₂ Γ = (pseudofunctor C).map₂ Δ := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
