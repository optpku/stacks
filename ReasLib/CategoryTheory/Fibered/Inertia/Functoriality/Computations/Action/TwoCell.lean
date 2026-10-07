module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# `2`-cell computations for the based-inertia pseudofunctor

This leaf identifies the packaged `2`-cell action with its canonical based-natural
transformation and exposes component and naturality formulas.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

/-- The ordinary pseudofunctor `2`-cell action is the explicit inertia `2`-morphism. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor two-cell computation"]
theorem pseudofunctor.map₂
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G) :
    (pseudofunctor C).map₂ η = Inertia.map₂ η := sorry

/-- Forgetting the packaged `2`-cell action recovers the explicit based natural transformation. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor two-cell underlying transformation"]
theorem pseudofunctor.map₂.toNatTrans
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G) :
    ((pseudofunctor C).map₂ η).toNatTrans = (Inertia.map₂ η).toNatTrans := sorry

/-- A component of the packaged `2`-cell action is the canonical intertwined component. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor two-cell component"]
theorem pseudofunctor.map₂.app
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y}
    (η : F ⟶ G) (A : (inertia X).obj) :
    ((pseudofunctor C).map₂ η).toNatTrans.app A =
      Inertia.map₂.component η A := sorry

/-- The ambient arrow underlying a packaged `2`-cell component is the original component. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor two-cell underlying component"]
theorem pseudofunctor.map₂.app.underlying
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y}
    (η : F ⟶ G) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom (((pseudofunctor C).map₂ η).toNatTrans.app A) =
      η.toNatTrans.app A.obj := sorry

/-- Every packaged based-inertia `2`-cell component is vertical over the identity on the base. -/
theorem pseudofunctor.map₂.app.isHomLift
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y}
    (η : F ⟶ G) (A : (inertia X).obj) :
    (inertia Y).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      (((pseudofunctor C).map₂ η).toNatTrans.app A) := sorry

/-- The packaged `2`-cell action is natural in inertia morphisms. -/
@[reassoc, stacks 04Z4 "based inertia pseudofunctor two-cell naturality"]
theorem pseudofunctor.map₂.naturality
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G)
    {A B : (inertia X).obj} (φ : A ⟶ B) :
    ((pseudofunctor C).map F).toFunctor.map φ ≫
        ((pseudofunctor C).map₂ η).toNatTrans.app B =
      ((pseudofunctor C).map₂ η).toNatTrans.app A ≫
        ((pseudofunctor C).map G).toFunctor.map φ := sorry

end Inertia

end BasedCategory
end CategoryTheory
