/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Cat.Basic

/-!
# Evaluation for the Cat-valued conical pseudolimit

An object of `ConicalPseudoLimit.apex F` is a strong transformation from the terminal
constant diagram to the resized diagram. Evaluating its components at a fixed object of the
terminal category gives the legs of the universal cone.

This file constructs those evaluation functors and their pseudonaturality isomorphisms. The
strong transformation and bilimit cone assembled from them live in the downstream cone layer.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe wJ vJ uJ vCat uCat

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.ConicalPseudoLimit

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

/-- A specified object of mathlib's chosen terminal category.

The terminal object of `Cat.{vCat, uCat}` is intentionally opaque, so its underlying type
does not expose an `Inhabited` instance. This definition obtains a point through the unique
functor from the explicit one-object model `ShrinkHoms PUnit`; it does not expose a raw
`Classical.choice`. -/
noncomputable def terminalPoint :
    (⊤_ Cat.{vCat, uCat}) :=
  (Limits.terminalIsTerminal.from
      (Cat.of (ShrinkHoms.{uCat} PUnit.{uCat + 1}) : Cat.{vCat, uCat})).toFunctor.obj
    (ShrinkHoms.toShrinkHoms PUnit.unit)

/-- Evaluation of identity modifications at `j` and `terminalPoint` is an identity. -/
private theorem evaluationMapId (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J)
    (η : apex F) :
    (((𝟙 η : η ⟶ η)).as.app j).toNatTrans.app terminalPoint =
      𝟙 ((η.app j).toFunctor.obj terminalPoint) := sorry

/-- Evaluation of modifications at `j` and `terminalPoint` preserves composition. -/
private theorem evaluationMapComp (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J)
    {η θ ι : apex F} (Γ : η ⟶ θ) (Δ : θ ⟶ ι) :
    ((Γ ≫ Δ).as.app j).toNatTrans.app terminalPoint =
      (Γ.as.app j).toNatTrans.app terminalPoint ≫
        (Δ.as.app j).toNatTrans.app terminalPoint := sorry

/-- Evaluate a terminal-apex pseudocone at the vertex `j`.

On objects this evaluates the component functor of a strong transformation at
`terminalPoint`; on arrows it evaluates the corresponding modification at the same point.
Thus all non-`Prop` data of the evaluation functor are explicit. -/
noncomputable def evaluation (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J) :
    apex F ⟶ (resizedDiagram F).obj j :=
  Functor.toCatHom
    { obj := fun η => (η.app j).toFunctor.obj terminalPoint
      map := fun Γ => (Γ.as.app j).toNatTrans.app terminalPoint
      map_id := evaluationMapId F j
      map_comp := evaluationMapComp F j }

/-- Evaluation on an apex object is component evaluation at `j` and `terminalPoint`. -/
@[simp]
theorem evaluation_obj (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J)
    (η : apex F) :
    (evaluation F j).toFunctor.obj η =
      (η.app j).toFunctor.obj terminalPoint := sorry

/-- Evaluation on an apex morphism is component evaluation at `j` and `terminalPoint`. -/
@[simp]
theorem evaluation_map (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J)
    {η θ : apex F} (Γ : η ⟶ θ) :
    (evaluation F j).toFunctor.map Γ =
      (Γ.as.app j).toNatTrans.app terminalPoint := sorry

/-- The component at a terminal-apex pseudocone of the naturality isomorphism between
evaluation functors. It is the original strong-naturality isomorphism evaluated at
`terminalPoint`. -/
private noncomputable def naturalityApp (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) (η : apex F) :
    ((Pseudofunctor.const J (apex F)).map f ≫ evaluation F b).toFunctor.obj η ≅
      (evaluation F a ≫ (resizedDiagram F).map f).toFunctor.obj η :=
  (Cat.Hom.toNatIso (η.naturality f)).app terminalPoint

/-- The objectwise evaluation isomorphisms are natural in modifications. -/
private theorem naturalityApp_naturality (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) :
    ∀ {η θ : apex F} (Γ : η ⟶ θ),
      ((Pseudofunctor.const J (apex F)).map f ≫ evaluation F b).toFunctor.map Γ ≫
        (naturalityApp F f θ).hom =
        (naturalityApp F f η).hom ≫
          (evaluation F a ≫ (resizedDiagram F).map f).toFunctor.map Γ := sorry

/-- Pseudonaturality of the evaluation functors along a `1`-morphism of `J`. -/
noncomputable def naturality (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) :
    (Pseudofunctor.const J (apex F)).map f ≫ evaluation F b ≅
      evaluation F a ≫ (resizedDiagram F).map f :=
  Cat.Hom.isoMk <| NatIso.ofComponents
    (naturalityApp F f) (naturalityApp_naturality F f)

/-- The forward component of evaluation pseudonaturality is the original strong-naturality
component evaluated at `terminalPoint`. -/
@[simp]
theorem naturality_hom_app (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) (η : apex F) :
    ((naturality F f).hom).toNatTrans.app η =
      ((Cat.Hom.toNatIso (η.naturality f)).app terminalPoint).hom := sorry

/-- The inverse component of evaluation pseudonaturality is the inverse original
strong-naturality component evaluated at `terminalPoint`. -/
@[simp]
theorem naturality_inv_app (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) (η : apex F) :
    ((naturality F f).inv).toNatTrans.app η =
      ((Cat.Hom.toNatIso (η.naturality f)).app terminalPoint).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`terminalPoint` is obtained by applying the canonical functor from an explicit one-object
category. `evaluation` gives its object and morphism actions directly, and `naturality`
evaluates the existing strong-naturality isomorphism componentwise. Any `sorryAx` dependency
is confined to functoriality, naturality, and inherited coherence fields. -/

end Bicategory.ConicalPseudoLimit

end CategoryTheory
