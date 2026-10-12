/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
        (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F).map φ := sorry

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

/-- Naturality of the canonical cone used to map pointwise left-derived values. -/
@[stacks 05SA]
theorem mapCone_naturality {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (g₁ g₂ : StructuredArrow (S.Q.obj Y) S.Q) (φ : g₁ ⟶ g₂) :
    limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
        (StructuredArrow.mk (S.Q.map f ≫ g₂.hom)) =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
          (StructuredArrow.mk (S.Q.map f ≫ g₁.hom)) ≫
        (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F).map φ := sorry

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
        (StructuredArrow.mk (S.Q.map f ≫ g.hom)) := sorry

/-- Morphisms into a pointwise left-derived value are determined by their composites with all
projections of its defining limit. -/
@[stacks 05SA, ext]
theorem hom_ext {X : D} [F.HasPointwiseLeftDerivedFunctorAt S X] {Z : D'}
    {f g : Z ⟶ obj F S X}
    (h : ∀ j : StructuredArrow (S.Q.obj X) S.Q,
      f ≫ limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) j =
        g ≫ limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) j) :
    f = g := sorry

/-- the canonical map of pointwise left-derived values sends an identity morphism to
the identity of the corresponding value, without requiring global pointwise definedness. -/
@[stacks 05SA, simp]
theorem map_id (X : D) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    map F S (𝟙 X) = 𝟙 (obj F S X) := sorry

/-- the canonical maps of pointwise left-derived values respect composition whenever
the three individual values are defined, without requiring a global derived functor. -/
@[stacks 05SA, simp]
theorem map_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S Z] :
    map F S (f ≫ g) = map F S f ≫ map F S g := sorry

/-- the map of pointwise left-derived values is compatible with every commutative
square of denominators. -/
@[stacks 05SA]
theorem map_comp_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    {X' Y' : D} (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq s f' f s') :
    CommSq (map F S f) (π F S s hs) (π F S s' hs') (F.map f') := sorry

/-- The equality form of denominator-square compatibility for pointwise left-derived maps. -/
@[stacks 05SA, reassoc]
theorem map_π_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    {X' Y' : D} (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq s f' f s') :
    map F S f ≫ π F S s' hs' = π F S s hs ≫ F.map f' := sorry

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
    φ = map F S f := sorry


end CategoryTheory.Functor.LeftDerived.Value
