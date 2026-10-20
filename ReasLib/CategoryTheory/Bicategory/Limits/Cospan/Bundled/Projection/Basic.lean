module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Modification
public import
  ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.Pseudofunctor.Basic
public import
  ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# The projection diagram of bundled bicategorical cospans

The three vertex projections and the two tautological legs of a bundled cospan are most
naturally owned by a single walking-cospan pseudofunctor valued in pseudofunctors. This file
constructs that neutral owner by restricting bicategorical evaluation along
`Cospan.inclusion`, and records its pointwise computation API.

Named endpoint projections are layered in `Cospan.Bundled.Projection`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]

variable (B) in
/-- The walking cospan of vertex-projection pseudofunctors on bundled cospans.

Its objects are evaluation at the left endpoint, right endpoint, and common target; its
generating `1`-morphisms are the two tautological cospan legs. The ambient bicategory is
explicit because this parameter-free owner has no bundled cospan from which to infer it. -/
@[stacks 0040 "projection diagram of bundled bicategorical cospans"]
def projectionDiagram :
    Pseudofunctor (LocallyDiscrete Limits.WalkingCospan)
      (Pseudofunctor (Cospan B) B) :=
  (Pseudofunctor.evaluation
      (LocallyDiscrete Limits.WalkingCospan) B).comp
    (Pseudofunctor.precomp B
      (inclusion B).toPseudofunctor).toPseudofunctor

/-- Evaluating the projection diagram at a vertex and a bundled cospan returns the
corresponding vertex of its walking-cospan diagram. -/
@[simp]
theorem projectionDiagram.eval.obj
    (a : LocallyDiscrete Limits.WalkingCospan) (S : Cospan B) :
    ((projectionDiagram B).obj a).obj S =
      S.diagram.obj a := sorry

/-- At a fixed vertex, the projection diagram maps a bundled-cospan morphism to the
corresponding component of its underlying strong transformation. -/
@[simp]
theorem projectionDiagram.eval.map
    (a : LocallyDiscrete Limits.WalkingCospan)
    {S T : Cospan B} (ψ : S ⟶ T) :
    ((projectionDiagram B).obj a).map ψ =
      (Hom.toCospanTransform ψ).app a := sorry

/-- At a fixed vertex, the projection diagram maps a bundled-cospan `2`-morphism to the
corresponding component of its underlying modification. -/
@[simp]
theorem projectionDiagram.eval.map₂
    (a : LocallyDiscrete Limits.WalkingCospan)
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    ((projectionDiagram B).obj a).map₂ Γ =
      (Hom₂.toModification Γ).as.app a := sorry

/-- The hom-functor at a vertex is inclusion into walking-cospan transformations followed by
component evaluation at that vertex. -/
@[simp]
theorem projectionDiagram.eval.mapFunctor
    (a : LocallyDiscrete Limits.WalkingCospan) (S T : Cospan B) :
    ((projectionDiagram B).obj a).mapFunctor S T =
      (inclusion B).mapFunctor S T ⋙
        Pseudofunctor.evaluationHom a S.diagram T.diagram := sorry

/-- Every vertex projection has the identity component isomorphism as its unit comparison. -/
@[simp]
theorem projectionDiagram.eval.mapId
    (a : LocallyDiscrete Limits.WalkingCospan) (S : Cospan B) :
    ((projectionDiagram B).obj a).mapId S =
      Iso.refl (𝟙 (S.diagram.obj a)) := sorry

/-- Every vertex projection has the identity component isomorphism as its composition
comparison. -/
@[simp]
theorem projectionDiagram.eval.mapComp
    (a : LocallyDiscrete Limits.WalkingCospan)
    {S T U : Cospan B} (ψ : S ⟶ T) (φ : T ⟶ U) :
    ((projectionDiagram B).obj a).mapComp ψ φ =
      Iso.refl
        ((Hom.toCospanTransform ψ).app a ≫
          (Hom.toCospanTransform φ).app a) := sorry

/-- A walking-cospan arrow acts on the projection diagram by applying each bundled cospan
diagram to that arrow. -/
@[simp]
theorem projectionDiagram.map.app
    {a b : LocallyDiscrete Limits.WalkingCospan}
    (h : a ⟶ b) (S : Cospan B) :
    ((projectionDiagram B).map h).app S =
      S.diagram.map h := sorry

/-- Naturality of a projection-diagram arrow is the inverse naturality isomorphism of the
underlying cospan transformation. -/
@[simp]
theorem projectionDiagram.map.naturality
    {a b : LocallyDiscrete Limits.WalkingCospan}
    (h : a ⟶ b) {S T : Cospan B} (ψ : S ⟶ T) :
    ((projectionDiagram B).map h).naturality ψ =
      ((Hom.toCospanTransform ψ).naturality h).symm := sorry

/-- A walking-cospan `2`-morphism acts pointwise through the `2`-morphism action of each
bundled cospan diagram. -/
@[simp]
theorem projectionDiagram.map₂.app
    {a b : LocallyDiscrete Limits.WalkingCospan}
    {h k : a ⟶ b} (γ : h ⟶ k) (S : Cospan B) :
    ((projectionDiagram B).map₂ γ).as.app S =
      S.diagram.map₂ γ := sorry

/-- The forward unit comparison of the projection diagram is pointwise the forward unit
comparison of the bundled cospan diagram. -/
@[simp]
theorem projectionDiagram.mapId.hom.app
    (a : LocallyDiscrete Limits.WalkingCospan) (S : Cospan B) :
    ((projectionDiagram B).mapId a).hom.as.app S =
      (S.diagram.mapId a).hom := sorry

/-- The inverse unit comparison of the projection diagram is pointwise the inverse unit
comparison of the bundled cospan diagram. -/
@[simp]
theorem projectionDiagram.mapId.inv.app
    (a : LocallyDiscrete Limits.WalkingCospan) (S : Cospan B) :
    ((projectionDiagram B).mapId a).inv.as.app S =
      (S.diagram.mapId a).inv := sorry

/-- The forward composition comparison of the projection diagram is pointwise the forward
composition comparison of the bundled cospan diagram. -/
@[simp]
theorem projectionDiagram.mapComp.hom.app
    {a b c : LocallyDiscrete Limits.WalkingCospan}
    (h : a ⟶ b) (k : b ⟶ c) (S : Cospan B) :
    ((projectionDiagram B).mapComp h k).hom.as.app S =
      (S.diagram.mapComp h k).hom := sorry

/-- The inverse composition comparison of the projection diagram is pointwise the inverse
composition comparison of the bundled cospan diagram. -/
@[simp]
theorem projectionDiagram.mapComp.inv.app
    {a b c : LocallyDiscrete Limits.WalkingCospan}
    (h : a ⟶ b) (k : b ⟶ c) (S : Cospan B) :
    ((projectionDiagram B).mapComp h k).inv.as.app S =
      (S.diagram.mapComp h k).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`projectionDiagram` is the composite of the existing evaluation pseudofunctor with
precomposition by `Cospan.inclusion`. It introduces no new component, comparison, or
representative choice. `#print axioms` reports `[propext, sorryAx, Classical.choice,
Quot.sound]`; the inherited `sorryAx` is confined to pseudofunctorial coherence and the
computation theorems above. -/

end CategoryTheory.Bicategory.Cospan
