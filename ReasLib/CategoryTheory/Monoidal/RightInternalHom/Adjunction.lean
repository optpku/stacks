/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic

/-!
# Adjunction calculus for chosen right internal Homs

This leaf exposes the curry/uncurry inverse laws, their three variable naturalities, useful
equality criteria, and the standard evaluation/coevaluation normal forms.
-/

@[expose] public section

universe v u

namespace CategoryTheory.RightInternalHom

open MonoidalCategory Opposite
open scoped CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (H : RightInternalHom C)

set_option backward.isDefEq.respectTransparency false

/-- The Hom-equivalence naturality needed to transport a chosen right internal-Hom adjunction
along a candidate left family `T ≅ tensoringRight`.  The comparison is explicit data; this theorem
is the sole deferred coherence obligation in `adjunctionOfIso`. -/
@[reassoc, stacks 0GWJ "right internal-Hom parametrized transport naturality"]
theorem adjunctionOfIso_homEquiv_naturality
    (T : C ⥤ C ⥤ C) (e : T ≅ tensoringRight C)
    {X Y : C} (f : X ⟶ Y) {W Z : C}
    (g : (T.obj Y).obj W ⟶ Z) :
    (((H.adj₂.adj X).ofNatIsoLeft (e.app X).symm).homEquiv W Z
        ((T.map f).app W ≫ g)) =
      (((H.adj₂.adj Y).ofNatIsoLeft (e.app Y).symm).homEquiv W Z g) ≫
        (H.hom.map f.op).app Z := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.symm_hom]
  change (H.adj₂.adj X).homEquiv W Z
      ((e.inv.app X).app W ≫ (T.map f).app W ≫ g) =
    (H.adj₂.adj Y).homEquiv W Z ((e.inv.app Y).app W ≫ g) ≫
      (H.hom.map f.op).app Z
  have hp := H.adj₂.homEquiv_naturality_one f ((e.app Y).inv.app W ≫ g)
  change (H.adj₂.adj X).homEquiv W Z
      (((tensoringRight C).map f).app W ≫ ((e.app Y).inv.app W ≫ g)) =
    (H.adj₂.adj Y).homEquiv W Z ((e.app Y).inv.app W ≫ g) ≫
      (H.hom.map f.op).app Z at hp
  have he := NatTrans.congr_app (e.inv.naturality f) W
  simp only [NatTrans.comp_app] at he
  rw [← reassoc_of% he]
  exact hp

/-- Transport the canonical right-tensor parametrized adjunction across an explicit natural
isomorphism `e : T ≅ tensoringRight`.  This is a genuine `ParametrizedAdjunction`; unlike a family
of unrelated pointwise adjunctions, its parameter naturality is exposed as the named theorem above.
-/
@[stacks 0GWJ "right internal-Hom parametrized adjunction transport"]
noncomputable def adjunctionOfIso
    (T : C ⥤ C ⥤ C) (e : T ≅ tensoringRight C) :
    T ⊣₂ H.hom :=
  ParametrizedAdjunction.mk'
    (fun X => (H.adj₂.adj X).ofNatIsoLeft (e.app X).symm)
    (fun {X Y} (f : X ⟶ Y) {W Z} (g : (T.obj Y).obj W ⟶ Z) =>
      adjunctionOfIso_homEquiv_naturality H T e f g)

/-- The adjunction bijection computes as currying. -/
theorem homEquiv_apply_eq {X W Y : C} (f : W ⊗ X ⟶ Y) :
    H.homEquiv X W Y f = H.curry f := by
  rfl

/-- The inverse adjunction bijection computes as uncurrying. -/
theorem homEquiv_symm_apply_eq {X W Y : C} (f : W ⟶ (X ⟶[H]ᵣ Y)) :
    (H.homEquiv X W Y).symm f = H.uncurry f := by
  rfl

/-- Currying is natural in the source `W`. -/
@[reassoc]
theorem curry_natural_left
    {X W W' Y : C} (f : W ⟶ W') (g : W' ⊗ X ⟶ Y) :
    H.curry (f ▷ X ≫ g) = f ≫ H.curry g := by
  change (H.adj₂.adj X).homEquiv W Y
      (((tensoringRight C).obj X).map f ≫ g) =
    f ≫ (H.adj₂.adj X).homEquiv W' Y g
  exact (H.adj₂.adj X).homEquiv_naturality_left f g

/-- Currying is natural in the target `Y`. -/
@[reassoc]
theorem curry_natural_right
    {X W Y Y' : C} (f : W ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    H.curry (f ≫ g) = H.curry f ≫ (H.hom.obj (op X)).map g := by
  change (H.adj₂.adj X).homEquiv W Y' (f ≫ g) =
    (H.adj₂.adj X).homEquiv W Y f ≫ (H.hom.obj (op X)).map g
  exact (H.adj₂.adj X).homEquiv_naturality_right f g

/-- Currying is natural in the internal-Hom parameter `X`. -/
@[reassoc]
theorem curry_natural_parameter
    {X X' W Y : C} (f : X ⟶ X') (g : W ⊗ X' ⟶ Y) :
    H.curry (W ◁ f ≫ g) = H.curry g ≫ (H.hom.map f.op).app Y := by
  change H.adj₂.homEquiv (((tensoringRight C).map f).app W ≫ g) =
    H.adj₂.homEquiv g ≫ (H.hom.map f.op).app Y
  exact H.adj₂.homEquiv_naturality_one f g

/-- Uncurrying is natural in the source `W`. -/
@[reassoc]
theorem uncurry_natural_left
    {X W W' Y : C} (f : W ⟶ W') (g : W' ⟶ (X ⟶[H]ᵣ Y)) :
    H.uncurry (f ≫ g) = f ▷ X ≫ H.uncurry g := by
  change ((H.adj₂.adj X).homEquiv W Y).symm (f ≫ g) =
    ((tensoringRight C).obj X).map f ≫
      ((H.adj₂.adj X).homEquiv W' Y).symm g
  exact (H.adj₂.adj X).homEquiv_naturality_left_symm f g

/-- Uncurrying is natural in the target `Y`. -/
@[reassoc]
theorem uncurry_natural_right
    {X W Y Y' : C} (f : W ⟶ (X ⟶[H]ᵣ Y)) (g : Y ⟶ Y') :
    H.uncurry (f ≫ (H.hom.obj (op X)).map g) = H.uncurry f ≫ g := by
  change ((H.adj₂.adj X).homEquiv W Y').symm
      (f ≫ (H.hom.obj (op X)).map g) =
    ((H.adj₂.adj X).homEquiv W Y).symm f ≫ g
  exact (H.adj₂.adj X).homEquiv_naturality_right_symm f g

/-- Uncurrying is natural in the internal-Hom parameter `X`. -/
@[reassoc]
theorem uncurry_natural_parameter
    {X X' W Y : C} (f : X ⟶ X') (g : W ⟶ (X' ⟶[H]ᵣ Y)) :
    H.uncurry (g ≫ (H.hom.map f.op).app Y) = W ◁ f ≫ H.uncurry g := by
  change H.adj₂.homEquiv.symm (g ≫ (H.hom.map f.op).app Y) =
    ((tensoringRight C).map f).app W ≫ H.adj₂.homEquiv.symm g
  exact H.adj₂.homEquiv_symm_naturality_one f g

/-- Uncurrying a curried map recovers the original map. -/
@[simp]
theorem uncurry_curry {X W Y : C} (f : W ⊗ X ⟶ Y) :
    H.uncurry (H.curry f) = f := by
  exact Equiv.symm_apply_apply (H.homEquiv X W Y) f

/-- Currying an uncurried map recovers the original map. -/
@[simp]
theorem curry_uncurry {X W Y : C} (f : W ⟶ (X ⟶[H]ᵣ Y)) :
    H.curry (H.uncurry f) = f := by
  exact Equiv.apply_symm_apply (H.homEquiv X W Y) f

/-- A map is the curry of another exactly when their uncurrying equality holds. -/
theorem curry_eq_iff {X W Y : C} (f : W ⊗ X ⟶ Y) (g : W ⟶ (X ⟶[H]ᵣ Y)) :
    H.curry f = g ↔ f = H.uncurry g := by
  constructor
  · intro h
    rw [← h]
    exact (uncurry_curry H f).symm
  · intro h
    rw [h]
    exact curry_uncurry H g

/-- The reverse form of `curry_eq_iff`. -/
theorem eq_curry_iff {X W Y : C} (f : W ⊗ X ⟶ Y) (g : W ⟶ (X ⟶[H]ᵣ Y)) :
    g = H.curry f ↔ H.uncurry g = f := by
  constructor
  · intro h
    rw [h]
    exact uncurry_curry H f
  · intro h
    calc
      g = H.curry (H.uncurry g) := (curry_uncurry H g).symm
      _ = H.curry f := congrArg H.curry h

/-- Uncurrying is evaluation after tensoring the input map on the right. -/
theorem uncurry_eq {X W Y : C} (f : W ⟶ (X ⟶[H]ᵣ Y)) :
    H.uncurry f = f ▷ X ≫ H.ev X Y := by
  change ((H.adj₂.adj X).homEquiv W Y).symm f =
    ((tensoringRight C).obj X).map f ≫ (H.adj₂.adj X).counit.app Y
  exact (H.adj₂.adj X).homEquiv_counit W Y f

/-- Currying is coevaluation followed by the right internal-Hom action on the target map. -/
theorem curry_eq {X W Y : C} (f : W ⊗ X ⟶ Y) :
    H.curry f = H.coev X W ≫ (H.hom.obj (op X)).map f := by
  change (H.adj₂.adj X).homEquiv W Y f =
    (H.adj₂.adj X).unit.app W ≫ (H.hom.obj (op X)).map f
  exact (H.adj₂.adj X).homEquiv_unit W Y f

/-- Currying is injective. -/
theorem curry_injective {X W Y : C} :
    Function.Injective (H.curry : (W ⊗ X ⟶ Y) → (W ⟶ (X ⟶[H]ᵣ Y))) := by
  exact (H.homEquiv X W Y).injective

/-- Uncurrying is injective. -/
theorem uncurry_injective {X W Y : C} :
    Function.Injective (H.uncurry : (W ⟶ (X ⟶[H]ᵣ Y)) → (W ⊗ X ⟶ Y)) := by
  exact (H.homEquiv X W Y).symm.injective

end CategoryTheory.RightInternalHom
