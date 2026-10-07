module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.Cofiltered
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Directed.Hom

/-!
# Presheaf-fiber maps of directed refinements

This file owns presheaf fibers and their maps for fixed-endpoint and bundled
directed refinements. The underlying object-fiber maps remain in `Hom` so
request transport can use that lower layer without importing cofiltered
presheaf support.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w r r' r'' q

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

namespace DirectedInverseSystem.RefinementHom

variable {C : Type u} [Category.{v} C]
variable {X : DirectedInverseSystem.{u, v, r, q} C}
variable {Y : DirectedInverseSystem.{u, v, r', q} C}
variable {Z : DirectedInverseSystem.{u, v, r'', q} C}

/-- The raw presheaf-fiber map induced by a fixed-endpoint refinement
morphism. -/
noncomputable def presheafFiberMap [LocallySmall.{q} C]
    (f : DirectedInverseSystem.RefinementHom X Y) :
    X.presheafFiber ⟶ Y.presheafFiber :=
  OrderedRefinement.EssentiallySmall.Cofiltered.presheafFiberMap f.toOrdered

/-- Forgetting endpoints induces the same cofiltered presheaf-fiber map as the
fixed-endpoint interface. -/
@[simp]
theorem toOrdered.presheafFiberMap [LocallySmall.{q} C]
    (f : DirectedInverseSystem.RefinementHom X Y) :
    OrderedRefinement.EssentiallySmall.Cofiltered.presheafFiberMap f.toOrdered =
      f.presheafFiberMap := sorry

/-- Presheaf-fiber maps of fixed-endpoint refinements commute with canonical
germs. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality [LocallySmall.{q} C]
    (f : DirectedInverseSystem.RefinementHom X Y) (F : Cᵒᵖ ⥤ Type q)
    (A : C) (x : X.fiber.obj A) :
    X.toPresheafFiber A x F ≫ f.presheafFiberMap.app F =
      Y.toPresheafFiber A (f.fiberMap.app A x) F := sorry

/-- The raw presheaf-fiber map of the identity fixed-endpoint refinement is
the identity. -/
@[simp]
theorem id.presheafFiberMap [LocallySmall.{q} C]
    (X : DirectedInverseSystem.{u, v, r, q} C) :
    (id X).presheafFiberMap = 𝟙 X.presheafFiber := sorry

/-- The raw presheaf-fiber map of a composite fixed-endpoint refinement is
the composite of its raw fiber maps. -/
@[simp]
theorem comp.presheafFiberMap [LocallySmall.{q} C]
    (f : DirectedInverseSystem.RefinementHom X Y)
    (g : DirectedInverseSystem.RefinementHom Y Z) :
    (f.comp g).presheafFiberMap = f.presheafFiberMap ≫ g.presheafFiberMap := sorry

end DirectedInverseSystem.RefinementHom

namespace DirectedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [Preorder ι] {S : ιᵒᵖ ⥤ C}

/-- The raw presheaf fiber of the source system, using the directed data
stored in a refinement. -/
noncomputable def sourcePresheafFiber [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    (Cᵒᵖ ⥤ Type q) ⥤ Type q :=
  R.sourceSystem.presheafFiber

/-- The raw presheaf fiber of the target system of a directed refinement. -/
noncomputable def targetPresheafFiber [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    (Cᵒᵖ ⥤ Type q) ⥤ Type q :=
  R.target.presheafFiber

/-- The map on raw presheaf fibers induced by a directed refinement. -/
noncomputable def presheafFiberMap [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.sourcePresheafFiber ⟶ R.targetPresheafFiber :=
  R.toRefinementHom.presheafFiberMap

/-- The fixed-endpoint bridge induces the same presheaf-fiber map as the
bundled directed refinement. -/
@[simp]
theorem toRefinementHom.presheafFiberMap [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.toRefinementHom.presheafFiberMap = R.presheafFiberMap := sorry

/-- Presheaf-fiber maps of directed refinements commute with canonical
germs. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (F : Cᵒᵖ ⥤ Type q) (A : C) (x : R.sourceFiber.obj A) :
    R.sourceSystem.toPresheafFiber A x F ≫ R.presheafFiberMap.app F =
      R.target.toPresheafFiber A (R.fiberMap.app A x) F := sorry

/-- The raw presheaf-fiber map of the identity refinement is the identity. -/
@[simp]
theorem id.presheafFiberMap [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) :
    (id T).presheafFiberMap = 𝟙 T.presheafFiber := sorry

/-- The raw presheaf-fiber map of a composite directed refinement is the
composite of the raw fiber maps. -/
@[simp]
theorem comp.presheafFiberMap [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram) :
    (R.comp Q).presheafFiberMap = R.presheafFiberMap ≫ Q.presheafFiberMap := sorry

/- Data audit: both presheaf-fiber maps inherit their non-Prop data from the
neutral ordered-refinement owner; any `sorryAx` is confined to naturality
proof fields. -/

end DirectedRefinement

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
