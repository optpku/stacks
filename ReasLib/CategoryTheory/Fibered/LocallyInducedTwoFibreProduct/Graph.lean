/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Equivalence
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graph equivalences for locally induced two-fibre products

The selected graph is lifted from the ambient graph. Its equivalence is obtained with the
generic locally induced equivalence constructor once the forward and inverse membership facts
have been supplied.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable {X Y : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}

section Graph

variable [detected : Projections.IsDetected (P := P) (Q := Q)]

include detected in
/-- The raw graph into a pseudo-pullback with an identity leg satisfies the selected hom
property whenever that property is detected by the two projections. -/
@[stacks 02XQ "membership of the graph into a locally induced two-fibre product"]
theorem graph.mem (F : X ⟶ Y) :
    Q X (apex F (𝟙 Y)) (BasedCategory.PseudoPullback.graph F.obj) := by
  apply Projections.IsDetected.mem F (𝟙 Y)
  · change Q X X (𝟙 X.1)
    exact Bicategory.HomProperty.IsMultiplicative.id_mem (Q := Q) X
  · change Q X Y F.obj
    exact F.property

/-- The graph of a selected morphism into its explicit two-fibre product with the identity. -/
@[stacks 02XQ "graph into a locally induced two-fibre product with an identity leg"]
def graph (F : X ⟶ Y) : X ⟶ apex F (𝟙 Y) :=
  Bicategory.LocallyInducedBicategory.mkHom
    (BasedCategory.PseudoPullback.graph F.obj) (graph.mem F)

/-- Forgetting the selected graph recovers the explicit based pseudo-pullback graph. -/
@[simp]
theorem graph.obj (F : X ⟶ Y) :
    (graph F).obj = BasedCategory.PseudoPullback.graph F.obj := rfl

section ProjectionReadout

variable [Projections.Has (P := P) (Q := Q)]

/-- The first projection of the locally induced graph is the identity. -/
@[simp]
theorem graph.fst (F : X ⟶ Y) :
    graph F ≫ fst F (𝟙 Y) = 𝟙 X := rfl

/-- The second projection of the locally induced graph is the original selected morphism. -/
@[simp]
theorem graph.snd (F : X ⟶ Y) :
    graph F ≫ snd F (𝟙 Y) = F := rfl

end ProjectionReadout

include detected in
/-- The forward morphism of the ambient graph equivalence satisfies the selected hom
property. -/
theorem graph.equivalence.hom.mem (F : X ⟶ Y) :
    Q X (apex F (𝟙 Y))
      (BasedCategory.PseudoPullback.graph.equivalence F.obj).hom :=
  graph.mem F

end Graph

section InverseMembership

variable [projections : Projections.Has (P := P) (Q := Q)]

include projections in
/-- The inverse morphism of the ambient graph equivalence satisfies the selected hom property
because it is the first pseudo-pullback projection. -/
theorem graph.equivalence.inv.mem (F : X ⟶ Y) :
    Q (apex F (𝟙 Y)) X
      (BasedCategory.PseudoPullback.graph.equivalence F.obj).inv :=
  Projections.Has.fst_mem F (𝟙 Y)

end InverseMembership

section Equivalence

variable [Projections.IsDetected (P := P) (Q := Q)]
variable [Projections.Has (P := P) (Q := Q)]

/-- The canonical equivalence from an object to its locally induced two-fibre product with an
identity leg. The generic locally induced lift retains the ambient graph inverse, unit, and
counit without rebuilding their coherence. -/
@[stacks 02XQ "graph equivalence in a locally induced two-fibre product"]
noncomputable def graph.equivalence (F : X ⟶ Y) : X ≌ apex F (𝟙 Y) :=
  Bicategory.LocallyInducedBicategory.equivalenceMk
    (BasedCategory.PseudoPullback.graph.equivalence F.obj)
    (graph.equivalence.hom.mem F) (graph.equivalence.inv.mem F)

/-- The forward `1`-morphism of the locally induced graph equivalence is the selected graph. -/
@[simp]
theorem graph.equivalence.hom (F : X ⟶ Y) :
    (graph.equivalence F).hom = graph F := rfl

/-- The inverse `1`-morphism of the locally induced graph equivalence is the selected first
projection. -/
@[simp]
theorem graph.equivalence.inv (F : X ⟶ Y) :
    (graph.equivalence F).inv =
      CategoryTheory.LocallyInduced.TwoFibreProduct.fst F (𝟙 Y) := rfl

/-- The unit of the locally induced graph equivalence is the ambient graph unit regarded in the
selected hom category. -/
@[simp]
theorem graph.equivalence.unit (F : X ⟶ Y) :
    (graph.equivalence F).unit =
      (Q X X).isoMk
        (BasedCategory.PseudoPullback.graph.equivalence F.obj).unit := rfl

/-- The counit of the locally induced graph equivalence is the ambient graph counit regarded in
the selected hom category. -/
@[simp]
theorem graph.equivalence.counit (F : X ⟶ Y) :
    (graph.equivalence F).counit =
      (Q (apex F (𝟙 Y)) (apex F (𝟙 Y))).isoMk
        (BasedCategory.PseudoPullback.graph.equivalence F.obj).counit := rfl

end Equivalence

/- Data audit: `graph.equivalence` retains the ambient non-`Prop` equivalence data through
`Bicategory.LocallyInducedBicategory.equivalenceMk`; the two named membership bridges above are
the only specialization-specific proof inputs. -/

end TwoFibreProduct
end LocallyInduced
end CategoryTheory
