/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.AssocLeftProjection.Computations

/-!
# The left-projection reassociation equivalence

Assembly and component API for the equivalence `K ⊡ (π₁ F G) ≌ (K ⋙ F) ⊡ G`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe vA' vA vB vD
universe uA' uA uB uD

namespace Limits.CategoricalPullback.LeftProjection

variable {A₀' : Type uA'} [Category.{vA'} A₀']
variable {A₀ : Type uA} [Category.{vA} A₀]
variable {B₀ : Type uB} [Category.{vB} B₀]
variable {D₀ : Type uD} [Category.{vD} D₀]

variable (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EquivalenceImplementation

/-- Coherence of the inner component of the reassociation unit. -/
private theorem unitSndComponentComm (x : K ⊡ (π₁ F G)) :
    F.map x.iso.inv ≫ ((forward K F G ⋙ inverse K F G).obj x).snd.iso.hom =
      x.snd.iso.hom ≫ G.map (𝟙 x.snd.snd) := sorry

/-- The inner categorical-pullback isomorphism in the explicit reassociation unit. -/
private def unitSndComponent (x : K ⊡ (π₁ F G)) :
    x.snd ≅ (forward K F G ⋙ inverse K F G).obj x |>.snd :=
  CategoricalPullback.mkIso x.iso.symm (Iso.refl _) (unitSndComponentComm K F G x)

/-- Coherence of the outer component of the reassociation unit. -/
private theorem unitComponentComm (x : K ⊡ (π₁ F G)) :
    K.map (𝟙 x.fst) ≫ ((forward K F G ⋙ inverse K F G).obj x).iso.hom =
      x.iso.hom ≫ (π₁ F G).map (unitSndComponent K F G x).hom := sorry

/-- Objectwise unit of the explicit reassociation equivalence. -/
private def unitComponent (x : K ⊡ (π₁ F G)) :
    x ≅ (forward K F G ⋙ inverse K F G).obj x :=
  CategoricalPullback.mkIso (Iso.refl _) (unitSndComponent K F G x)
    (unitComponentComm K F G x)

/-- Naturality of the explicit reassociation unit components. -/
private theorem unitNaturality {x y : K ⊡ (π₁ F G)} (φ : x ⟶ y) :
    φ ≫ (unitComponent K F G y).hom =
      (unitComponent K F G x).hom ≫ (forward K F G ⋙ inverse K F G).map φ := sorry

/-- Unit natural isomorphism of the explicit reassociation equivalence. -/
private def unitIso :
    𝟭 (K ⊡ (π₁ F G)) ≅ forward K F G ⋙ inverse K F G :=
  NatIso.ofComponents (unitComponent K F G) (unitNaturality K F G)

/-- Coherence of the reassociation counit component. -/
private theorem counitComponentComm (x : (K ⋙ F) ⊡ G) :
    (K ⋙ F).map (𝟙 x.fst) ≫ x.iso.hom =
      ((inverse K F G ⋙ forward K F G).obj x).iso.hom ≫ G.map (𝟙 x.snd) := sorry

/-- Objectwise counit of the explicit reassociation equivalence. -/
private def counitComponent (x : (K ⋙ F) ⊡ G) :
    (inverse K F G ⋙ forward K F G).obj x ≅ x :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (counitComponentComm K F G x)

/-- Naturality of the explicit reassociation counit components. -/
private theorem counitNaturality {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    (inverse K F G ⋙ forward K F G).map φ ≫ (counitComponent K F G y).hom =
      (counitComponent K F G x).hom ≫ φ := sorry

/-- Counit natural isomorphism of the explicit reassociation equivalence. -/
private def counitIso :
    inverse K F G ⋙ forward K F G ≅ 𝟭 ((K ⋙ F) ⊡ G) :=
  NatIso.ofComponents (counitComponent K F G) (counitNaturality K F G)

/-- Triangle coherence for the explicit reassociation unit and counit. -/
private theorem triangle (x : K ⊡ (π₁ F G)) :
    (forward K F G).map ((unitIso K F G).hom.app x) ≫
        (counitIso K F G).hom.app ((forward K F G).obj x) =
      𝟙 ((forward K F G).obj x) := sorry

end EquivalenceImplementation

/-- A reusable left-projection specialization of categorical-pullback reassociation: there is a
canonical equivalence `K ⊡ (π₁ F G) ≌ (K ⋙ F) ⊡ G`.

The forward and inverse data are explicit; proof debt is confined to compatibility, naturality,
and triangle fields. -/
def equivalence : K ⊡ (π₁ F G) ≌ (K ⋙ F) ⊡ G where
  functor := forward K F G
  inverse := inverse K F G
  unitIso := EquivalenceImplementation.unitIso K F G
  counitIso := EquivalenceImplementation.counitIso K F G
  functor_unitIso_comp := EquivalenceImplementation.triangle K F G

namespace equivalence

/-- The forward functor of left-projection reassociation is the explicit forward normalization. -/
@[simp]
theorem functor :
    (LeftProjection.equivalence K F G).functor = LeftProjection.forward K F G := sorry

/-- The inverse functor of left-projection reassociation is the explicit inverse normalization. -/
@[simp]
theorem inverse :
    (LeftProjection.equivalence K F G).inverse = LeftProjection.inverse K F G := sorry

/-- The reassociation unit is the identity on the outer left component. -/
@[simp]
theorem unitIso.hom.app.fst (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.equivalence K F G).unitIso.hom.app x).fst = 𝟙 x.fst := sorry

/-- The reassociation unit uses the inverse outer comparison on the inserted inner left
component. -/
@[simp]
theorem unitIso.hom.app.sndFst (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.equivalence K F G).unitIso.hom.app x).snd.fst = x.iso.inv := sorry

/-- The reassociation unit is the identity on the inner right component. -/
@[simp]
theorem unitIso.hom.app.sndSnd (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.equivalence K F G).unitIso.hom.app x).snd.snd =
      𝟙 x.snd.snd := sorry

/-- The inverse reassociation unit is the identity on the outer left component. -/
@[simp]
theorem unitIso.inv.app.fst (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.equivalence K F G).unitIso.inv.app x).fst = 𝟙 x.fst := sorry

/-- The inverse reassociation unit uses the outer comparison on the inserted inner left
component. -/
@[simp]
theorem unitIso.inv.app.sndFst (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.equivalence K F G).unitIso.inv.app x).snd.fst = x.iso.hom := sorry

/-- The inverse reassociation unit is the identity on the inner right component. -/
@[simp]
theorem unitIso.inv.app.sndSnd (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.equivalence K F G).unitIso.inv.app x).snd.snd =
      𝟙 x.snd.snd := sorry

/-- The reassociation counit is the identity on its left component. -/
@[simp]
theorem counitIso.hom.app.fst (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.equivalence K F G).counitIso.hom.app x).fst = 𝟙 x.fst := sorry

/-- The reassociation counit is the identity on its right component. -/
@[simp]
theorem counitIso.hom.app.snd (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.equivalence K F G).counitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- The inverse reassociation counit is the identity on its left component. -/
@[simp]
theorem counitIso.inv.app.fst (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.equivalence K F G).counitIso.inv.app x).fst = 𝟙 x.fst := sorry

/-- The inverse reassociation counit is the identity on its right component. -/
@[simp]
theorem counitIso.inv.app.snd (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.equivalence K F G).counitIso.inv.app x).snd = 𝟙 x.snd := sorry

end equivalence

namespace forward

/-- The explicit forward reassociation is an equivalence of categories. -/
@[instance]
theorem isEquivalence : (LeftProjection.forward K F G).IsEquivalence := sorry

end forward

namespace inverse

/-- The explicit inverse reassociation is an equivalence of categories. -/
@[instance]
theorem isEquivalence : (LeftProjection.inverse K F G).IsEquivalence := sorry

end inverse

end Limits.CategoricalPullback.LeftProjection

end CategoryTheory
