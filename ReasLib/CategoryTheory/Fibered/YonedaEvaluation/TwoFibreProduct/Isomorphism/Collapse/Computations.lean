/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse.Inverse

/-!
# Collapse and inverse computation rules

Object, morphism, and projection formulas for the collapse functor and its deterministic inverse.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

namespace collapse

/-- Object-level computation for the collapse into the category of elements of the lifted
isomorphism presheaf. -/
@[simp, stacks 04SI "collapse object computation"]
theorem obj (Q : (source X x y).obj) :
    (collapse X x y).obj Q = op (element X x y Q) := sorry

/-- Morphism-level computation for the collapse functor. -/
@[simp, stacks 04SI "collapse morphism computation"]
theorem map {Q R : (source X x y).obj} (f : Q ⟶ R) :
    (collapse X x y).map f =
      Quiver.Hom.op
        (CategoryOfElements.homMk (element X x y R) (element X x y Q)
          ((sourceProjection X x y).map f).op
          (isomSection.ulift.naturality X x y f)) := sorry

/-- The collapse commutes with the projection to the slice category. -/
@[simp, stacks 04SI "collapse projection"]
theorem comp_projection :
    (collapse X x y).toFunctor ⋙ projection X x y =
      sourceProjection X x y := sorry

/-- The projection of a collapsed object is the displayed slice object of the literal source. -/
@[simp, stacks 04SI "collapse object projection"]
theorem obj_projection (Q : (source X x y).obj) :
    (projection X x y).obj ((collapse X x y).toFunctor.obj Q) =
      (sourceProjection X x y).obj Q := sorry

/-- Projecting the image of a literal morphism recovers its source-projection map. -/
@[simp, stacks 04SI "collapse map projection"]
theorem map_projection {Q R : (source X x y).obj} (f : Q ⟶ R) :
    (projection X x y).map ((collapse X x y).toFunctor.map f) =
      eqToHom (obj_projection X x y Q) ≫
        (sourceProjection X x y).map f ≫
          eqToHom (obj_projection X x y R).symm := sorry

namespace inverse

/-- Object-level computation for the deterministic inverse functor. -/
@[simp, stacks 04SI "inverse object computation"]
theorem obj (q : total X x y) :
    (collapse.inverse X x y).toFunctor.obj q = object X x y q := sorry

/-- Morphism-level computation for the deterministic inverse functor. -/
@[simp, stacks 04SI "inverse morphism computation"]
theorem map_eq {q r : total X x y} (f : q ⟶ r) :
    (collapse.inverse X x y).toFunctor.map f = map X x y f := sorry

/-- The outer comparison stored by the deterministic inverse object is the selected
relative-product comparison. -/
@[simp, stacks 04SI "inverse comparison readout"]
theorem obj_comparison (q : total X x y) :
    BasedCategory.PseudoPullback.comparison
        ((collapse.inverse X x y).toFunctor.obj q) =
      (comparisonIso X x y q).hom := sorry

/-- The common base component of the deterministic inverse map is the displayed slice-source
map. -/
@[simp, stacks 04SI "inverse base map readout"]
theorem map_base {q r : total X x y} (f : q ⟶ r) :
    BasedCategory.PseudoPullback.baseMap
        ((collapse.inverse X x y).toFunctor.map f) =
      baseMap X x y f := sorry

/-- The deterministic inverse commutes with the projection to the slice category. -/
@[simp, stacks 04SI "inverse projection"]
theorem comp_projection :
    (inverse X x y).toFunctor ⋙ sourceProjection X x y =
      projection X x y := sorry

/-- The middle object selected by the deterministic inverse is the left Yoneda value at the
displayed slice object. -/
@[simp, stacks 04SI "inverse middle object"]
theorem obj_middle (q : total X x y) :
    BasedCategory.PseudoPullback.fstObj ((inverse X x y).toFunctor.obj q) =
      (yonedaMap X x).obj ((projection X x y).obj q) := sorry

/-- The slice object selected by the deterministic inverse is the displayed Grothendieck base. -/
@[simp, stacks 04SI "inverse slice object"]
theorem obj_slice (q : total X x y) :
    BasedCategory.PseudoPullback.sndObj ((inverse X x y).toFunctor.obj q) =
      (projection X x y).obj q := sorry

/-- The middle component of the deterministic inverse map is the left Yoneda image of the
displayed base map. -/
@[simp, stacks 04SI "inverse middle map"]
theorem map_middle {q r : total X x y} (f : q ⟶ r) :
    BasedCategory.PseudoPullback.fstMap ((inverse X x y).toFunctor.map f) =
      eqToHom (obj_middle X x y q) ≫
        (yonedaMap X x).map ((projection X x y).map f) ≫
          eqToHom (obj_middle X x y r).symm := sorry

/-- The slice component of the deterministic inverse map is the displayed Grothendieck base
map. -/
@[simp, stacks 04SI "inverse slice map"]
theorem map_slice {q r : total X x y} (f : q ⟶ r) :
    BasedCategory.PseudoPullback.sndMap ((inverse X x y).toFunctor.map f) =
      eqToHom (obj_slice X x y q) ≫
        (projection X x y).map f ≫
          eqToHom (obj_slice X x y r).symm := sorry

end inverse
end collapse
end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
