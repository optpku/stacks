/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.CategoryTheory.Functor.PresheafFiber

/-!
# Fibers of left Kan extensions of presheaves

This leaf identifies the presheaf fiber of a left Kan extension with the
fiber for the composite type-valued functor. It is an adjoint-uniqueness
calculation, independent of sites and of any particular point.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Lemma 7.34.1 (0F4F): taking the fiber for `v` after left Kan extension along `u.op`
is canonically isomorphic to taking the fiber for the composite `u ⋙ v`. -/
@[stacks 0F4F]
noncomputable def lanCompPresheafFiberIso
    (u : C ⥤ D) (v : D ⥤ Type w)
    [HasColimitsOfShape v.Elementsᵒᵖ (Type w)]
    [HasColimitsOfShape (u ⋙ v).Elementsᵒᵖ (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F] :
    (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w) ⋙ v.presheafFiber ≅
      (u ⋙ v).presheafFiber :=
  Adjunction.leftAdjointUniq ((u.op.lanAdjunction (Type w)).comp v.presheafFiberCostalkAdj)
    ((u ⋙ v).presheafFiberCostalkAdj)

end CategoryTheory.Functor
