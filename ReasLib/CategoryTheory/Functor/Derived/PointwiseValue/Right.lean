/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointwise Right-Derived Values

This leaf owns the concrete colimit presentation of a pointwise right-derived value and its
functoriality at individually defined objects.  It requires no ambient derived category and no
global pointwise-definedness hypothesis.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Value

open Limits

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/-- pointwise right-derived definedness supplies the colimit used to construct the
right-derived value at `X`. -/
@[stacks 05SA]
noncomputable instance hasColimit (X : D) [F.HasPointwiseRightDerivedFunctorAt S X] :
    HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
  Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X

/-- the pointwise right-derived value of `F` at `X`, presented as the colimit over
the costructured-arrow category of `S.Q` above `X`. -/
@[stacks 05SA]
noncomputable abbrev obj (X : D) [F.HasPointwiseRightDerivedFunctorAt S X] : D' :=
  colimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)

/-- the canonical map from `F.obj X'` to the pointwise right-derived value at `X`
associated to a denominator `s : X ⟶ X'` in `S`. -/
@[stacks 05SA]
noncomputable abbrev ι {X X' : D} (s : X ⟶ X') (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X] : F.obj X' ⟶ obj F S X :=
  colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
    (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))

/-- The raw constant-functor naturality equation used to construct the right-derived-value
mapping cocone. -/
@[stacks 05SA]
theorem mapCocone_naturality_raw {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    (g₁ g₂ : CostructuredArrow S.Q (S.Q.obj X)) (φ : g₁ ⟶ g₂) :
    (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F).map φ ≫
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
          (CostructuredArrow.mk (g₂.hom ≫ S.Q.map f)) =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
        (CostructuredArrow.mk (g₁.hom ≫ S.Q.map f)) ≫
          ((Functor.const (CostructuredArrow S.Q (S.Q.obj X))).obj (obj F S Y)).map φ := by
  set_option backward.isDefEq.respectTransparency false in
    rw [Functor.const_obj_map, Category.comp_id]
    exact colimit.w (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
      ((CostructuredArrow.map (S.Q.map f)).map φ)

/-- The canonical cocone on the right-derived-value diagram which induces the map along `f`. -/
@[stacks 05SA]
noncomputable def mapCocone {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y] :
    Cocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
  Cocone.mk (obj F S Y)
    { app := fun g ↦
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
          (CostructuredArrow.mk (g.hom ≫ S.Q.map f))
      naturality := fun g₁ g₂ φ ↦ mapCocone_naturality_raw F S f g₁ g₂ φ }

/-- Naturality of the canonical cocone used to map pointwise right-derived values. -/
@[stacks 05SA]
theorem mapCocone_naturality {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    (g₁ g₂ : CostructuredArrow S.Q (S.Q.obj X)) (φ : g₁ ⟶ g₂) :
    (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F).map φ ≫
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
          (CostructuredArrow.mk (g₂.hom ≫ S.Q.map f)) =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
        (CostructuredArrow.mk (g₁.hom ≫ S.Q.map f)) :=
  (mapCocone F S f).w φ

/-- the canonical map between pointwise right-derived values induced by `f`. -/
@[stacks 05SA]
noncomputable def map {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y] :
    obj F S X ⟶ obj F S Y :=
  colimit.desc _ (mapCocone F S f)

/-- The map of pointwise right-derived values is computed on every colimit leg by
postcomposing the corresponding localized arrow with `S.Q.map f`. -/
@[stacks 05SA, reassoc]
theorem ι_map {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    (g : CostructuredArrow S.Q (S.Q.obj X)) :
    colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) g ≫ map F S f =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F)
        (CostructuredArrow.mk (g.hom ≫ S.Q.map f)) :=
  colimit.ι_desc (mapCocone F S f) g

/-- Morphisms out of a pointwise right-derived value are determined by their composites with
all legs of its defining colimit. -/
@[stacks 05SA, ext]
theorem hom_ext {X : D} [F.HasPointwiseRightDerivedFunctorAt S X] {Z : D'}
    {f g : obj F S X ⟶ Z}
    (h : ∀ j : CostructuredArrow S.Q (S.Q.obj X),
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫ f =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫ g) :
    f = g :=
  colimit.hom_ext h

/-- the canonical map of pointwise right-derived values sends an identity morphism
to the identity of the corresponding value, without requiring global pointwise definedness. -/
@[stacks 05SA, simp]
theorem map_id (X : D) [F.HasPointwiseRightDerivedFunctorAt S X] :
    map F S (𝟙 X) = 𝟙 (obj F S X) := by
  set_option backward.isDefEq.respectTransparency false in
    apply hom_ext F S
    intro j
    rw [ι_map, S.Q.map_id, Category.comp_id, Category.comp_id]
    rfl

/-- the canonical maps of pointwise right-derived values respect composition whenever
the three individual values are defined, without requiring a global derived functor. -/
@[stacks 05SA, simp]
theorem map_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S Z] :
    map F S (f ≫ g) = map F S f ≫ map F S g := by
  set_option backward.isDefEq.respectTransparency false in
    apply hom_ext F S
    intro j
    rw [ι_map, ← Category.assoc, ι_map, ι_map, S.Q.map_comp]
    let leg (k : S.Q.obj j.left ⟶ S.Q.obj Z) : F.obj j.left ⟶ obj F S Z :=
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Z) ⋙ F) (CostructuredArrow.mk k)
    change leg (j.hom ≫ S.Q.map f ≫ S.Q.map g) =
      leg ((j.hom ≫ S.Q.map f) ≫ S.Q.map g)
    exact congrArg leg (Category.assoc j.hom (S.Q.map f) (S.Q.map g)).symm

/-- the map of pointwise right-derived values is compatible with every commutative
square of denominators. -/
@[stacks 05SA]
theorem map_comp_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    {X' Y' : D} (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq f s s' f') :
    CommSq (ι F S s hs) (F.map f') (map F S f) (ι F S s' hs') := by
  let u : CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv ≫ S.Q.map f) ⟶
      CostructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv) :=
    CostructuredArrow.homMk f' (by
      apply (Localization.isoOfHom S.Q S s hs).eq_inv_comp.mpr
      change S.Q.map s ≫ (S.Q.map f' ≫ (Localization.isoOfHom S.Q S s' hs').inv) =
        S.Q.map f
      rw [← Category.assoc, ← S.Q.map_comp, ← sq.w, S.Q.map_comp,
        Category.assoc, Localization.isoOfHom_hom_inv_id, Category.comp_id])
  exact ⟨(ι_map F S f _).trans (colimit.w _ u).symm⟩

/-- The equality form of denominator-square compatibility for pointwise right-derived maps. -/
@[stacks 05SA, reassoc]
theorem ι_map_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    {X' Y' : D} (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq f s s' f') :
    ι F S s hs ≫ map F S f = F.map f' ≫ ι F S s' hs' :=
  (map_comp_of_square F S f s s' hs hs' f' sq).w

/-- denominator-square compatibility characterizes the canonical map between
pointwise right-derived values. -/
@[stacks 05SA]
theorem map_hom_ext {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
    {φ : obj F S X ⟶ obj F S Y}
    (hφ : ∀ ⦃X' Y' : D⦄ (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq f s s' f'),
          CommSq (ι F S s hs) (F.map f') φ (ι F S s' hs')) :
    φ = map F S f := by
  set_option backward.isDefEq.respectTransparency false in
    apply hom_ext F S
    intro j
    obtain ⟨a, ha⟩ := Localization.exists_leftFraction S.Q S j.hom
    let u : j ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S a.s a.hs).inv) :=
      CostructuredArrow.homMk a.f ha.symm
    have hj : F.map a.f ≫ ι F S a.s a.hs =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j :=
      colimit.w (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) u
    obtain ⟨b, hb⟩ :=
      (MorphismProperty.RightFraction.mk a.s a.hs f).exists_leftFraction
    have sq : CommSq f a.s b.s b.f := ⟨hb⟩
    have hleg : ι F S a.s a.hs ≫ φ = ι F S a.s a.hs ≫ map F S f :=
      (hφ a.s b.s a.hs b.hs b.f sq).w.trans
        (ι_map_of_square F S f a.s b.s a.hs b.hs b.f sq).symm
    calc
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫ φ =
          F.map a.f ≫ (ι F S a.s a.hs ≫ φ) := by
        rw [← hj, Category.assoc]
      _ = F.map a.f ≫ (ι F S a.s a.hs ≫ map F S f) := by rw [hleg]
      _ = colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫ map F S f := by
        rw [← Category.assoc, hj]


end CategoryTheory.Functor.RightDerived.Value
