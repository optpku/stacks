module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Unit for the graph into an identity pseudo-pullback

This leaf packages the componentwise identity isomorphism from a based category to the graph
followed by the first projection, including its naturality, verticality, and based natural
isomorphism API.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory.PseudoPullback

open Functor.Fiber
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

noncomputable section

/-- The component of the graph unit is the identity isomorphism on the original object. -/
@[stacks 0040 "graph unit component"]
noncomputable def graph.unitComponent (F : X ⥤ᵇ Y) (x : X.obj) :
    x ≅ ((graph F) ⋙ PseudoPullback.fst F (𝟭 Y)).obj x :=
  Iso.refl _

/-- The forward arrow of each graph-unit component is the identity. -/
@[simp]
theorem graph.unitComponent.hom (F : X ⥤ᵇ Y) (x : X.obj) :
    (graph.unitComponent F x).hom = 𝟙 x := sorry

/-- The inverse arrow of each graph-unit component is the identity. -/
@[simp]
theorem graph.unitComponent.inv (F : X ⥤ᵇ Y) (x : X.obj) :
    (graph.unitComponent F x).inv = 𝟙 x := sorry

/-- The identity graph-unit components are natural in source morphisms. -/
theorem graph.unitComponent.naturality (F : X ⥤ᵇ Y)
    {x y : X.obj} (a : x ⟶ y) :
    a ≫ (graph.unitComponent F y).hom =
      (graph.unitComponent F x).hom ≫
        ((graph F) ⋙ PseudoPullback.fst F (𝟭 Y)).map a := sorry

/-- Every forward graph-unit component is vertical over the identity of the source base
object. -/
theorem graph.unitComponent.isHomLift (F : X ⥤ᵇ Y) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x)) (graph.unitComponent F x).hom := sorry

/-- The identity based functor is canonically isomorphic, componentwise, to the graph followed by
the first projection. -/
@[stacks 0040 "unit of the graph equivalence for an explicit pseudo-pullback"]
noncomputable def graph.unitIso (F : X ⥤ᵇ Y) :
    𝟭 X ≅ graph F ⋙ PseudoPullback.fst F (𝟭 Y) :=
  BasedNatIso.ofComponents
    (graph.unitComponent F)
    (fun a ↦ graph.unitComponent.naturality F a)
    (graph.unitComponent.isHomLift F)

/-- The forward component of the based graph unit is the explicit identity component. -/
@[simp]
theorem graph.unitIso.hom.app (F : X ⥤ᵇ Y) (x : X.obj) :
    (graph.unitIso F).hom.app x =
      (graph.unitComponent F x).hom := sorry

/-- The inverse component of the based graph unit is the inverse explicit identity component. -/
@[simp]
theorem graph.unitIso.inv.app (F : X ⥤ᵇ Y) (x : X.obj) :
    (graph.unitIso F).inv.app x =
      (graph.unitComponent F x).inv := sorry

end

end BasedCategory.PseudoPullback
end CategoryTheory
