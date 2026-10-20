module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Counit for the graph into an identity pseudo-pullback

This leaf constructs the explicit counit from the first projection followed by the graph to the
identity.  It exposes the underlying component isomorphisms, their projection computations,
naturality, and the resulting based natural isomorphism.
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

/-- The graph retraction and the original pseudo-pullback object have the same base object. -/
theorem graph.counitObj.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    baseObj (((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).obj P) =
      baseObj P := sorry

/-- The graph retraction and the original pseudo-pullback object have the same first
component. -/
theorem graph.counitObj.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    fstObj (((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).obj P) =
      fstObj P := sorry

/-- The base isomorphism used by the graph counit. -/
noncomputable def graph.counitComponent.baseIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    baseObj (((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).obj P) ≅
      baseObj P :=
  fstBaseIso P

/-- The first-component isomorphism used by the graph counit. -/
noncomputable def graph.counitComponent.fstIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    fstObj (((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).obj P) ≅
      fstObj P :=
  Iso.refl _

/-- The forward first-component map of the graph counit is the identity. -/
@[simp]
theorem graph.counitComponent.fstIso.hom (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    (graph.counitComponent.fstIso F P).hom =
      𝟙 (fstObj P) := sorry

/-- The inverse first-component map of the graph counit is the identity. -/
@[simp]
theorem graph.counitComponent.fstIso.inv (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    (graph.counitComponent.fstIso F P).inv =
      𝟙 (fstObj P) := sorry

/-- The forward first-component isomorphism of the graph counit lies over its forward base
isomorphism. -/
theorem graph.counitComponent.fstIso.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    X.p.IsHomLift (graph.counitComponent.baseIso F P).hom
      (graph.counitComponent.fstIso F P).hom := sorry

/-- The forward structural comparison of the graph counit lies over its forward base
isomorphism. -/
theorem graph.counitComponent.snd.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    Y.p.IsHomLift (graph.counitComponent.baseIso F P).hom
      (comparisonIsoApp P).hom := sorry

/-- The component isomorphisms of the graph counit respect the structural comparisons of the
source and target pseudo-pullback objects. -/
theorem graph.counitComponent.compatibility (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    CommSq
      (F.toFunctor.map (graph.counitComponent.fstIso F P).hom)
      (comparison (((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).obj P))
      (comparison P)
      ((𝟭 Y).toFunctor.map (comparisonIsoApp P).hom) := sorry

/-- The component of the canonical counit identifying graph retraction with the identity on the
identity pseudo-pullback. -/
@[stacks 0040 "graph counit component"]
noncomputable def graph.counitComponent (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    ((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).obj P ≅ P :=
  mkIso (graph.counitComponent.baseIso F P)
    (graph.counitComponent.fstIso F P) (comparisonIsoApp P)
    (hom_fst := graph.counitComponent.fstIso.isHomLift F P)
    (hom_snd := graph.counitComponent.snd.isHomLift F P)
    (graph.counitComponent.compatibility F P)

/-- The base component of the forward graph-counit morphism is the canonical equality
isomorphism on the retained base object. -/
@[simp]
theorem graph.counitComponent.hom.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    baseMap (graph.counitComponent F P).hom =
      (graph.counitComponent.baseIso F P).hom := sorry

/-- The first component of the forward graph-counit morphism is the canonical equality
isomorphism on the retained first object. -/
@[simp]
theorem graph.counitComponent.hom.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    fstMap (graph.counitComponent F P).hom =
      (graph.counitComponent.fstIso F P).hom := sorry

/-- The second component of the forward graph-counit morphism is the structural comparison
isomorphism carried by the pseudo-pullback object. -/
@[simp]
theorem graph.counitComponent.hom.snd (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    sndMap (graph.counitComponent F P).hom =
      (comparisonIsoApp P).hom := sorry

/-- The base component of the inverse graph-counit morphism is the inverse canonical equality
isomorphism on the retained base object. -/
@[simp]
theorem graph.counitComponent.inv.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    baseMap (graph.counitComponent F P).inv =
      (graph.counitComponent.baseIso F P).inv := sorry

/-- The first component of the inverse graph-counit morphism is the inverse canonical equality
isomorphism on the retained first object. -/
@[simp]
theorem graph.counitComponent.inv.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    fstMap (graph.counitComponent F P).inv =
      (graph.counitComponent.fstIso F P).inv := sorry

/-- The second component of the inverse graph-counit morphism is the inverse structural
comparison isomorphism carried by the pseudo-pullback object. -/
@[simp]
theorem graph.counitComponent.inv.snd (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    sndMap (graph.counitComponent F P).inv =
      (comparisonIsoApp P).inv := sorry

/-- The graph counit components are natural in pseudo-pullback morphisms. -/
theorem graph.counitComponent.naturality (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback F (𝟭 Y)).obj} (φ : P ⟶ Q) :
    ((PseudoPullback.fst F (𝟭 Y)) ⋙ graph F).map φ ≫
        (graph.counitComponent F Q).hom =
      (graph.counitComponent F P).hom ≫ φ := sorry

/-- Every forward component of the graph counit is vertical over the unchanged base object. -/
theorem graph.counitComponent.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    (PseudoPullback F (𝟭 Y)).p.IsHomLift
      (𝟙 ((PseudoPullback F (𝟭 Y)).p.obj P))
      (graph.counitComponent F P).hom := sorry

/-- The first projection followed by the graph is canonically isomorphic, over the base, to the
identity on the identity pseudo-pullback. -/
@[stacks 0040 "counit of the graph equivalence for an explicit pseudo-pullback"]
noncomputable def graph.counitIso (F : X ⥤ᵇ Y) :
    PseudoPullback.fst F (𝟭 Y) ⋙ graph F ≅
      𝟭 (PseudoPullback F (𝟭 Y)) :=
  BasedNatIso.ofComponents
    (graph.counitComponent F)
    (fun φ ↦ graph.counitComponent.naturality F φ)
    (graph.counitComponent.isHomLift F)

/-- The forward component of the based graph counit is the explicit pseudo-pullback
isomorphism. -/
@[simp]
theorem graph.counitIso.hom.app (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    (graph.counitIso F).hom.app P =
      (graph.counitComponent F P).hom := sorry

/-- The inverse component of the based graph counit is the inverse explicit pseudo-pullback
isomorphism. -/
@[simp]
theorem graph.counitIso.inv.app (F : X ⥤ᵇ Y)
    (P : (PseudoPullback F (𝟭 Y)).obj) :
    (graph.counitIso F).inv.app P =
      (graph.counitComponent F P).inv := sorry

end

end BasedCategory.PseudoPullback
end CategoryTheory
