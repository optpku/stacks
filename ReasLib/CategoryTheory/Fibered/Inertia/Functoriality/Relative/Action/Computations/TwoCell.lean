/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.TwoCell

import Mathlib.Tactic.CrossRefAttribute

/-!
# `2`-cell computations for relative inertia

This leaf exposes component, underlying-arrow, naturality, and extensionality formulas for the
pseudo-comma relative-inertia `2`-cell action.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

namespace map₂

/-- Evaluation of the induced relative-inertia `2`-morphism is the explicit intertwining
component. -/
@[simp, stacks 04Z4 "relative-inertia 2-cell application"]
theorem app {f g : S ⟶ T} (η : f ⟶ g) (A : (relativeInertia S.hom).obj) :
    (map₂ η).toNatTrans.app A = component η A := sorry

/-- Every packaged pseudo-comma `2`-cell component is vertical over the unchanged source-base
object. -/
@[stacks 04Z4 "relative-inertia packaged 2-cell verticality"]
theorem app.isHomLift {f g : S ⟶ T} (η : f ⟶ g)
    (A : (relativeInertia S.hom).obj) :
    (relativeInertia T.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((map₂ η).toNatTrans.app A) := sorry

/-- The underlying arrow of the explicit relative-inertia component is the left endpoint
component of the original pseudo-comma `2`-morphism. -/
@[simp, stacks 04Z4 "relative-inertia explicit 2-cell underlying arrow"]
theorem component.underlying {f g : S ⟶ T} (η : f ⟶ g)
    (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom (component η A) =
      (Bicategory.PseudoComma.left₂ η).toNatTrans.app A.obj := sorry

/-- The underlying arrow of a pseudo-comma relative-inertia `2`-cell component is the left
endpoint component of the original `2`-morphism. -/
@[simp, stacks 04Z4 "relative-inertia packaged 2-cell underlying arrow"]
theorem app.underlying {f g : S ⟶ T} (η : f ⟶ g)
    (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom ((map₂ η).toNatTrans.app A) =
      (Bicategory.PseudoComma.left₂ η).toNatTrans.app A.obj := sorry

/-- The relative-inertia action on pseudo-comma `2`-morphisms is natural in relative-inertia
morphisms. -/
@[reassoc, stacks 04Z4 "relative-inertia 2-cell computation naturality"]
theorem naturality {f g : S ⟶ T} (η : f ⟶ g)
    {A B : (relativeInertia S.hom).obj} (φ : A ⟶ B) :
    (map f).toFunctor.map φ ≫ (map₂ η).toNatTrans.app B =
      (map₂ η).toNatTrans.app A ≫ (map g).toFunctor.map φ := sorry

/-- Two induced relative-inertia `2`-morphisms agree when all of their components agree. -/
@[stacks 04Z4 "relative-inertia 2-cell extensionality"]
theorem ext {f g : S ⟶ T} {η θ : f ⟶ g}
    (h : ∀ A : (relativeInertia S.hom).obj,
      (map₂ η).toNatTrans.app A = (map₂ θ).toNatTrans.app A) :
    map₂ η = map₂ θ := sorry

end map₂

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
