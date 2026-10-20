module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction.Action

/-!
# Pointwise `2`-cell action of the explicit pseudo-pullback pseudofunctor

Component formulas for the action on bundled cospan `2`-cells. Naturality and extensionality are
kept in the focused `Computations.Naturality` leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open CategoricalPullback
open scoped Bicategory

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The component of the bundled pseudofunctor action on a cospan 2-cell is the explicit
pseudo-pullback component. -/
@[simp]
theorem pseudofunctor.map₂.app
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor C).map₂ Γ).toNatTrans.app P =
      _root_.CategoryTheory.BasedCategory.PseudoPullback.map₂.component
        (Bicategory.Cospan.Hom₂.toBasedModification Γ) P := sorry

/-- The base component of the bundled pseudofunctor action on a cospan 2-cell is the identity. -/
@[simp]
theorem pseudofunctor.map₂.app.base
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) (P : (PseudoPullback S.fst S.snd).obj) :
    baseMap (((pseudofunctor C).map₂ Γ).toNatTrans.app P) =
      𝟙 (baseObj P) := sorry

/-- The first component of the bundled pseudofunctor action on a cospan 2-cell is its left
cospan component. -/
@[simp]
theorem pseudofunctor.map₂.app.fst
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) (P : (PseudoPullback S.fst S.snd).obj) :
    fstMap (((pseudofunctor C).map₂ Γ).toNatTrans.app P) =
      (Bicategory.Cospan.Hom₂.left Γ).toNatTrans.app (fstObj P) := sorry

/-- The second component of the bundled pseudofunctor action on a cospan 2-cell is its right
cospan component. -/
@[simp]
theorem pseudofunctor.map₂.app.snd
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) (P : (PseudoPullback S.fst S.snd).obj) :
    sndMap (((pseudofunctor C).map₂ Γ).toNatTrans.app P) =
      (Bicategory.Cospan.Hom₂.right Γ).toNatTrans.app (sndObj P) := sorry

/-- Every component of the bundled pseudo-pullback `2`-cell action is vertical over the
identity of the common base object. -/
theorem pseudofunctor.map₂.app.isHomLift
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) (P : (PseudoPullback S.fst S.snd).obj) :
    (PseudoPullback T.fst T.snd).p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      (((pseudofunctor C).map₂ Γ).toNatTrans.app P) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
