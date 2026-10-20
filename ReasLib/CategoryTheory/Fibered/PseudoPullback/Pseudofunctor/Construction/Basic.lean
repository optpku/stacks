/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Bicategorical
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# The explicit pseudo-pullback pseudofunctor

The bundled-cospan pseudofunctor, built from the existing object, morphism, and `2`-cell
actions together with their comparison and coherence data.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

universe u v w vB

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

namespace pseudofunctorConstruction

/-- The explicit pseudo-pullback apex assigned to a bundled based cospan. -/
private def objOwner
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    BasedCategory.{max v vB, max w (max u (max v vB))} C :=
  PseudoPullback S.fst S.snd

/-- The explicit pseudo-pullback map assigned to a morphism of bundled based cospans. -/
private def mapOwner
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) : objOwner S ⟶ objOwner T :=
  map (Bicategory.Cospan.Hom.toBasedTransform ψ)

/-- The explicit pseudo-pullback `2`-morphism assigned to a `2`-morphism of bundled based
cospans. -/
private def map₂Owner
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
  mapOwner ψ ⟶ mapOwner φ :=
  _root_.CategoryTheory.BasedCategory.PseudoPullback.map₂
    (Bicategory.Cospan.Hom₂.toBasedModification Γ)

/-- The bundled pseudo-pullback `2`-cell action preserves identity cells. -/
private theorem map₂Owner_id
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    map₂Owner (𝟙 ψ) = 𝟙 (mapOwner ψ) := sorry

/-- The bundled pseudo-pullback `2`-cell action preserves vertical composition. -/
private theorem map₂Owner_comp
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ χ : S ⟶ T} (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    map₂Owner (Γ ≫ Δ) = map₂Owner Γ ≫ map₂Owner Δ := sorry

/-- The hom functor of the bundled explicit pseudo-pullback action. -/
private def homFunctorOwner
    (S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (S ⟶ T) ⥤ (objOwner S ⟶ objOwner T) where
  obj := mapOwner
  map := map₂Owner
  map_id := map₂Owner_id
  map_comp := map₂Owner_comp

/-- The prelax core of the bundled explicit pseudo-pullback action. -/
private def prelax :
    PrelaxFunctor
      (Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
      (BasedCategory.{max v vB, max w (max u (max v vB))} C) :=
  PrelaxFunctor.mkOfHomFunctors objOwner homFunctorOwner

/-- The identity comparison of the bundled explicit pseudo-pullback action. -/
private noncomputable def mapIdOwner
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    prelax.map (𝟙 S) ≅ 𝟙 (prelax.obj S) :=
  eqToIso (congrArg map (Bicategory.Cospan.Hom.toBasedTransform.id S)) ≪≫
    map.idIso S.fst S.snd

/-- The composition comparison of the bundled explicit pseudo-pullback action. -/
private noncomputable def mapCompOwner
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    prelax.map (ψ ≫ φ) ≅ prelax.map ψ ≫ prelax.map φ :=
  eqToIso (congrArg map (Bicategory.Cospan.Hom.toBasedTransform.comp ψ φ)) ≪≫
    map.compIso
      (Bicategory.Cospan.Hom.toBasedTransform ψ)
      (Bicategory.Cospan.Hom.toBasedTransform φ)

/-- The bundled explicit pseudo-pullback action preserves left whiskering up to its canonical
composition comparisons. -/
private theorem map₂_whisker_left
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) {φ χ : S ⟶ T} (Γ : φ ⟶ χ) :
    prelax.map₂ (ψ ◁ Γ) =
      (mapCompOwner ψ φ).hom ≫
        prelax.map ψ ◁ prelax.map₂ Γ ≫
          (mapCompOwner ψ χ).inv := sorry

/-- The bundled explicit pseudo-pullback action preserves right whiskering up to its canonical
composition comparisons. -/
private theorem map₂_whisker_right
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : R ⟶ S} (Γ : ψ ⟶ φ) (χ : S ⟶ T) :
    prelax.map₂ (Γ ▷ χ) =
      (mapCompOwner ψ χ).hom ≫
        prelax.map₂ Γ ▷ prelax.map χ ≫
          (mapCompOwner φ χ).inv := sorry

/-- The bundled explicit pseudo-pullback action carries associators to associators with the
canonical composition comparisons. -/
private theorem map₂_associator
    {Q R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : Q ⟶ R) (φ : R ⟶ S) (χ : S ⟶ T) :
    prelax.map₂ (α_ ψ φ χ).hom =
      (mapCompOwner (ψ ≫ φ) χ).hom ≫
        (mapCompOwner ψ φ).hom ▷ prelax.map χ ≫
          (α_ (prelax.map ψ) (prelax.map φ) (prelax.map χ)).hom ≫
            prelax.map ψ ◁ (mapCompOwner φ χ).inv ≫
              (mapCompOwner ψ (φ ≫ χ)).inv := sorry

/-- The bundled explicit pseudo-pullback action carries left unitors to left unitors with the
canonical identity and composition comparisons. -/
private theorem map₂_left_unitor
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    prelax.map₂ (λ_ ψ).hom =
      (mapCompOwner (𝟙 S) ψ).hom ≫
        (mapIdOwner S).hom ▷ prelax.map ψ ≫
          (λ_ (prelax.map ψ)).hom := sorry

/-- The bundled explicit pseudo-pullback action carries right unitors to right unitors with the
canonical identity and composition comparisons. -/
private theorem map₂_right_unitor
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    prelax.map₂ (ρ_ ψ).hom =
      (mapCompOwner ψ (𝟙 T)).hom ≫
        prelax.map ψ ◁ (mapIdOwner T).hom ≫
          (ρ_ (prelax.map ψ)).hom := sorry

end pseudofunctorConstruction

variable (C) in
/-- The explicit pseudo-pullback construction as a pseudofunctor on bundled based cospans.

The object action is `PseudoPullback S.fst S.snd`; the `1`- and `2`-cell actions reuse the
existing computational `map` and `map₂`. Its comparison isomorphisms transport across the
canonical bundled-cospan bridge and then use `map.idIso` and `map.compIso`. Thus the
pseudofunctor adds no new semantic payload beyond packaging the already explicit action and its
coherence laws. The base category is explicit because this owner has no value input from which
Lean can recover it. -/
@[stacks 0040 "explicit pseudo-pullback pseudofunctor on bundled cospans"]
noncomputable def pseudofunctor :
    Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C) ⥤ᵖ
      BasedCategory.{max v vB, max w (max u (max v vB))} C where
  toPrelaxFunctor := pseudofunctorConstruction.prelax
  mapId := pseudofunctorConstruction.mapIdOwner
  mapComp := pseudofunctorConstruction.mapCompOwner
  map₂_whisker_left := pseudofunctorConstruction.map₂_whisker_left
  map₂_whisker_right := pseudofunctorConstruction.map₂_whisker_right
  map₂_associator := pseudofunctorConstruction.map₂_associator
  map₂_left_unitor := pseudofunctorConstruction.map₂_left_unitor
  map₂_right_unitor := pseudofunctorConstruction.map₂_right_unitor

end

end PseudoPullback

end BasedCategory

end CategoryTheory
