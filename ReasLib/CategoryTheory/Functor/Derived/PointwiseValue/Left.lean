/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointwise Left-Derived Values

This leaf owns the concrete limit presentation of a pointwise left-derived value and its
functoriality at individually defined objects.  It requires no ambient derived category and no
global pointwise-definedness hypothesis.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LeftDerived.Value

open Limits

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/-- pointwise left-derived definedness supplies the limit used to construct the
left-derived value at `X`. -/
@[stacks 05SA]
noncomputable instance hasLimit (X : D) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    HasLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
  Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X

/-- the pointwise left-derived value of `F` at `X`, presented as the limit over
the structured-arrow category of `S.Q` under `X`. -/
@[stacks 05SA]
noncomputable abbrev obj (X : D) [F.HasPointwiseLeftDerivedFunctorAt S X] : D' :=
  limit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)

/-- the canonical projection from the pointwise left-derived value at `X` to
`F.obj X'` associated to a denominator `s : X' ⟶ X` in `S`. -/
@[stacks 05SA]
noncomputable abbrev π {X X' : D} (s : X' ⟶ X) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S X] : obj F S X ⟶ F.obj X' :=
  limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
    (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))

set_option backward.isDefEq.respectTransparency false in
/-- The raw constant-functor naturality equation used to construct the left-derived-value mapping
cone. -/
@[stacks 05SA]
theorem mapCone_naturality_raw {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (g₁ g₂ : StructuredArrow (S.Q.obj Y) S.Q) (φ : g₁ ⟶ g₂) :
    ((Functor.const (StructuredArrow (S.Q.obj Y) S.Q)).obj (obj F S X)).map φ ≫
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
        (StructuredArrow.mk (S.Q.map f ≫ g₂.hom)) =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
          (StructuredArrow.mk (S.Q.map f ≫ g₁.hom)) ≫
        (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F).map φ := by
  exact (limit.cone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)).π.naturality
    ((StructuredArrow.map (S.Q.map f)).map φ)

/-- The canonical cone on the left-derived-value diagram which induces the map along `f`. -/
@[stacks 05SA]
noncomputable def mapCone {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    Cone (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F) :=
  Cone.mk (obj F S X)
    { app := fun g ↦
        limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
          (StructuredArrow.mk (S.Q.map f ≫ g.hom))
      naturality := fun g₁ g₂ φ ↦ mapCone_naturality_raw F S f g₁ g₂ φ }

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical cone used to map pointwise left-derived values. -/
@[stacks 05SA]
theorem mapCone_naturality {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (g₁ g₂ : StructuredArrow (S.Q.obj Y) S.Q) (φ : g₁ ⟶ g₂) :
    limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
        (StructuredArrow.mk (S.Q.map f ≫ g₂.hom)) =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
          (StructuredArrow.mk (S.Q.map f ≫ g₁.hom)) ≫
        (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F).map φ := by
  exact ((mapCone F S f).w φ).symm

/-- the canonical map between pointwise left-derived values induced by `f`. -/
@[stacks 05SA]
noncomputable def map {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    obj F S X ⟶ obj F S Y :=
  limit.lift _ (mapCone F S f)

/-- The map of pointwise left-derived values is computed on every limit projection by
precomposing the corresponding localized arrow with `S.Q.map f`. -/
@[stacks 05SA, reassoc]
theorem map_π {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (g : StructuredArrow (S.Q.obj Y) S.Q) :
    map F S f ≫ limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F) g =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
        (StructuredArrow.mk (S.Q.map f ≫ g.hom)) := by
  exact limit.lift_π (mapCone F S f) g

/-- Morphisms into a pointwise left-derived value are determined by their composites with all
projections of its defining limit. -/
@[stacks 05SA, ext]
theorem hom_ext {X : D} [F.HasPointwiseLeftDerivedFunctorAt S X] {Z : D'}
    {f g : Z ⟶ obj F S X}
    (h : ∀ j : StructuredArrow (S.Q.obj X) S.Q,
      f ≫ limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) j =
        g ≫ limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) j) :
    f = g := by
  exact limit.hom_ext h

/-- the canonical map of pointwise left-derived values sends an identity morphism to
the identity of the corresponding value, without requiring global pointwise definedness. -/
@[stacks 05SA, simp]
theorem map_id (X : D) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    map F S (𝟙 X) = 𝟙 (obj F S X) := by
  apply hom_ext F S
  intro j
  dsimp only [obj]
  rw [map_π, S.Q.map_id, Category.id_comp, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- the canonical maps of pointwise left-derived values respect composition whenever
the three individual values are defined, without requiring a global derived functor. -/
@[stacks 05SA, simp]
theorem map_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S Z] :
    map F S (f ≫ g) = map F S f ≫ map F S g := by
  apply hom_ext F S
  intro j
  dsimp only [obj]
  rw [map_π, Category.assoc, map_π, map_π, S.Q.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- the map of pointwise left-derived values is compatible with every commutative
square of denominators. -/
@[stacks 05SA]
theorem map_comp_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    {X' Y' : D} (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq s f' f s') :
    CommSq (map F S f) (π F S s hs) (π F S s' hs') (F.map f') := by
  have hsq : (Localization.isoOfHom S.Q S s hs).inv ≫ S.Q.map f' =
      S.Q.map f ≫ (Localization.isoOfHom S.Q S s' hs').inv := by
    apply (cancel_epi (Localization.isoOfHom S.Q S s hs).hom).1
    apply (cancel_mono (Localization.isoOfHom S.Q S s' hs').hom).1
    simpa only [Category.assoc, Localization.isoOfHom_hom,
      Localization.isoOfHom_hom_inv_id_assoc, Localization.isoOfHom_inv_hom_id,
      Category.comp_id] using (S.Q.map_commSq sq).w.symm
  refine ⟨?_⟩
  dsimp only [π]
  rw [map_π]
  exact (limit.w (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
    (show StructuredArrow.mk (Localization.isoOfHom S.Q S s hs).inv ⟶
      StructuredArrow.mk (S.Q.map f ≫ (Localization.isoOfHom S.Q S s' hs').inv) from
        StructuredArrow.homMk f' hsq)).symm

/-- The equality form of denominator-square compatibility for pointwise left-derived maps. -/
@[stacks 05SA, reassoc]
theorem map_π_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    {X' Y' : D} (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq s f' f s') :
    map F S f ≫ π F S s' hs' = π F S s hs ≫ F.map f' := by
  exact (map_comp_of_square F S f s s' hs hs' f' sq).w

set_option backward.isDefEq.respectTransparency false in
/-- denominator-square compatibility characterizes the canonical map between
pointwise left-derived values. -/
@[stacks 05SA]
theorem map_hom_ext {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    {φ : obj F S X ⟶ obj F S Y}
    (hφ : ∀ ⦃X' Y' : D⦄ (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq s f' f s'),
          CommSq φ (π F S s hs) (π F S s' hs') (F.map f')) :
    φ = map F S f := by
  apply hom_ext F S
  intro j
  obtain ⟨z, hz⟩ := Localization.exists_rightFraction S.Q S j.hom
  let t : StructuredArrow.mk (Localization.isoOfHom S.Q S z.s z.hs).inv ⟶ j :=
    StructuredArrow.homMk z.f (by
      change (Localization.isoOfHom S.Q S z.s z.hs).inv ≫ S.Q.map z.f = j.hom
      rw [hz]
      rfl)
  have hw : π F S z.s z.hs ≫ F.map z.f =
      limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F) j := by
    exact limit.w (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F) t
  obtain ⟨w, hw'⟩ :=
    (MorphismProperty.LeftFraction.mk f z.s z.hs).exists_rightFraction
  have sq : CommSq w.s w.f f z.s := ⟨hw'⟩
  have hden : φ ≫ π F S z.s z.hs = map F S f ≫ π F S z.s z.hs :=
    (hφ w.s z.s w.hs z.hs w.f sq).w.trans
      (map_π_of_square F S f w.s z.s w.hs z.hs w.f sq).symm
  simpa only [Category.assoc, hw] using congrArg (fun k ↦ k ≫ F.map z.f) hden


end CategoryTheory.Functor.LeftDerived.Value
