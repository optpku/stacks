/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence.Presheaf
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Equivalence

/-!
# Discrete-fibration-side Grothendieck comparison

This leaf owns the explicit comparison `toPresheaf ⋙ ofPresheaf ≅ 𝟭`, built from fiber-object
evaluation and the tautological reconstruction.
-/

@[expose] public section

universe w u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets.PresheafEquivalence

namespace ofObjIso

/-- Evaluation as a morphism from the Grothendieck construction of the fiber-object presheaf back
to the original category fibred in sets. -/
@[stacks 02Y2 "fiber-object evaluation comparison"]
noncomputable def hom
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    (ofPresheaf C).obj ((toPresheaf C).obj X) ⟶ X :=
  ofBasedFunctor (Functor.fiberObjectPresheaf.basedStrictIso X.p).hom

/-- The tautological inverse morphism, sending a total object to its fiber element over its own
image in the base. -/
@[stacks 02Y2 "fiber-object tautological comparison"]
noncomputable def inv
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    X ⟶ (ofPresheaf C).obj ((toPresheaf C).obj X) :=
  ofBasedFunctor (Functor.fiberObjectPresheaf.basedStrictIso X.p).inv

/- Axiom audit: the underlying total functors of these two morphisms are respectively the explicit
evaluation and tautological functors. Deferred dependencies occur only in proof-valued owner
membership and projection-compatibility fields. -/

/-- The total functor underlying `PresheafEquivalence.ofObjIso.hom` is the canonical evaluation
functor. -/
@[simp]
theorem hom.toFunctor
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    toFunctor (hom X) = Functor.fiberObjectPresheaf.evaluation X.p := rfl

/-- The total functor underlying `PresheafEquivalence.ofObjIso.inv` is the tautological
functor. -/
@[simp]
theorem inv.toFunctor
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    toFunctor (inv X) = Functor.fiberObjectPresheaf.unit X.p := rfl

/-- Evaluation followed by the tautological morphism is the identity morphism of the
Grothendieck construction. -/
theorem hom.comp_inv
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    hom X ≫ inv X =
      𝟙 ((ofPresheaf C).obj ((toPresheaf C).obj X)) := by
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedFunctor.ext
  exact Functor.fiberObjectPresheaf.evaluation.comp_unit X.p

/-- The tautological morphism followed by evaluation is the identity morphism of the original
category fibred in sets. -/
theorem inv.comp_hom
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    inv X ≫ hom X = 𝟙 X := by
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedFunctor.ext
  exact Functor.fiberObjectPresheaf.unit.comp_evaluation X.p

end ofObjIso

/-- Objectwise comparison `ofPresheaf (toPresheaf X) ≅ X`, with explicit evaluation and
tautological morphisms. -/
@[stacks 02Y2 "discrete-fibration-side object comparison"]
noncomputable def ofObjIso
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    (ofPresheaf C).obj ((toPresheaf C).obj X) ≅ X where
  hom := ofObjIso.hom X
  inv := ofObjIso.inv X
  hom_inv_id := ofObjIso.hom.comp_inv X
  inv_hom_id := ofObjIso.inv.comp_hom X

/- Axiom audit: the two morphism fields have the explicit total functors above. `sorryAx` is
confined to their proof-valued owner fields and the two inverse equations. -/

namespace ofObjIso

/-- The forward morphism of `PresheafEquivalence.ofObjIso` is evaluation. -/
@[simp]
theorem hom.eq
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    (ofObjIso X).hom = hom X := rfl

/-- The inverse morphism of `PresheafEquivalence.ofObjIso` is the tautological construction. -/
@[simp]
theorem inv.eq
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    (ofObjIso X).inv = inv X := rfl

/-- The evaluation comparisons are natural in morphisms of categories fibred in sets. -/
theorem naturality
    {X Y : FiberedCategoryOver.Sets.{u, v, max w u, v} C} (F : X ⟶ Y) :
    ((toPresheaf C ⋙ ofPresheaf C).map F) ≫ (ofObjIso Y).hom =
      (ofObjIso X).hom ≫ F := by
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedFunctor.ext
  refine Functor.hext (fun _ => rfl) ?_
  intro x y φ
  apply heq_of_eq
  apply Y.p.map_injective
  exact (Functor.congr_hom
    (comm (((toPresheaf C ⋙ ofPresheaf C).map F) ≫ (ofObjIso Y).hom)) φ).trans
      (Functor.congr_hom (comm ((ofObjIso X).hom ≫ F)) φ).symm

end ofObjIso

variable (C) in
/-- The canonical comparison `toPresheaf ⋙ ofPresheaf ≅ 𝟭` on the size-stable category of
discrete fibrations. Its components compute by evaluation and the tautological
category-of-elements construction. -/
@[stacks 02Y2 "discrete-fibration-side Grothendieck comparison"]
noncomputable def toIso :
    (toPresheaf C ⋙ ofPresheaf C :
      FiberedCategoryOver.Sets.{u, v, max w u, v} C ⥤
        FiberedCategoryOver.Sets.{u, v, max w u, v} C) ≅
      𝟭 (FiberedCategoryOver.Sets.{u, v, max w u, v} C) :=
  NatIso.ofComponents
    (fun X => ofObjIso X)
    (fun F => ofObjIso.naturality F)

/- Axiom audit: component morphisms are the explicit evaluation and tautological owners.
Deferred dependencies occur only in proof-valued laws and naturality. -/

namespace toIso

/-- The forward component of `PresheafEquivalence.toIso` is the evaluation comparison. -/
@[simp]
theorem hom.app
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    (toIso C).hom.app X = (ofObjIso X).hom := rfl

/-- The inverse component of `PresheafEquivalence.toIso` is the tautological comparison. -/
@[simp]
theorem inv.app
    (X : FiberedCategoryOver.Sets.{u, v, max w u, v} C) :
    (toIso C).inv.app X = (ofObjIso X).inv := rfl

end toIso

end FiberedCategoryOver.Sets.PresheafEquivalence

end CategoryTheory
