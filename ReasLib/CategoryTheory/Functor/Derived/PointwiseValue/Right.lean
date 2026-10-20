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
          ((Functor.const (CostructuredArrow S.Q (S.Q.obj X))).obj (obj F S Y)).map φ := sorry

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
        (CostructuredArrow.mk (g₁.hom ≫ S.Q.map f)) := sorry

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
        (CostructuredArrow.mk (g.hom ≫ S.Q.map f)) := sorry

/-- Morphisms out of a pointwise right-derived value are determined by their composites with
all legs of its defining colimit. -/
@[stacks 05SA, ext]
theorem hom_ext {X : D} [F.HasPointwiseRightDerivedFunctorAt S X] {Z : D'}
    {f g : obj F S X ⟶ Z}
    (h : ∀ j : CostructuredArrow S.Q (S.Q.obj X),
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫ f =
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫ g) :
    f = g := sorry

/-- the canonical map of pointwise right-derived values sends an identity morphism
to the identity of the corresponding value, without requiring global pointwise definedness. -/
@[stacks 05SA, simp]
theorem map_id (X : D) [F.HasPointwiseRightDerivedFunctorAt S X] :
    map F S (𝟙 X) = 𝟙 (obj F S X) := sorry

/-- the canonical maps of pointwise right-derived values respect composition whenever
the three individual values are defined, without requiring a global derived functor. -/
@[stacks 05SA, simp]
theorem map_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S Z] :
    map F S (f ≫ g) = map F S f ≫ map F S g := sorry

/-- the map of pointwise right-derived values is compatible with every commutative
square of denominators. -/
@[stacks 05SA]
theorem map_comp_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    {X' Y' : D} (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq f s s' f') :
    CommSq (ι F S s hs) (F.map f') (map F S f) (ι F S s' hs') := sorry

/-- The equality form of denominator-square compatibility for pointwise right-derived maps. -/
@[stacks 05SA, reassoc]
theorem ι_map_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    {X' Y' : D} (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq f s s' f') :
    ι F S s hs ≫ map F S f = F.map f' ≫ ι F S s' hs' := sorry

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
    φ = map F S f := sorry


end CategoryTheory.Functor.RightDerived.Value
