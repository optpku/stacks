module

-- Import decisions:
-- * `Categorical.Basic` owns the ordinary categorical pseudo-pullback and the deterministic
--   comparison construction.
-- * `PseudoPullback.Projections` supplies the explicit based pseudo-pullback and its two
--   projection functors without importing fibredness or inverse-choice infrastructure.
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections

/-!
# Deterministic comparison with a categorical pseudo-pullback

This leaf owns the comparison functor from the explicit same-fibre pseudo-pullback in `Cat/C`
to mathlib's ordinary categorical pullback.  It deliberately contains no fibredness hypothesis:
the functor, its object/map computations, and its compatibility with the common base are all
deterministic data.  The choice-dependent equivalence API belongs in
`PseudoPullback.Comparison.Equivalence`.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ

namespace CategoryTheory

open BasedCategory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open Functor
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

namespace BasedCategory.PseudoPullback.Comparison

/-- The canonical comparison from the explicit two-fibre product over `C` to the ordinary
categorical pullback of the underlying functors. This deterministic data is an opaque API owner;
clients should use its projection compatibility rather than depend on unfolding its constructor. -/
@[stacks 0H2E "explicit-to-categorical pseudo-pullback comparison"]
def functor
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ⥤ F.toFunctor ⊡ G.toFunctor :=
  (toFunctorToCategoricalPullback F.toFunctor G.toFunctor
    (PseudoPullback F G).obj).obj (PseudoPullback.square F G)

/-- The first projection of the deterministic comparison is the first explicit
pseudo-pullback projection. -/
@[simp]
theorem functor.fst
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    functor F G ⋙ π₁ F.toFunctor G.toFunctor =
      (PseudoPullback.fst F G).toFunctor := sorry

/-- The second projection of the deterministic comparison is the second explicit
pseudo-pullback projection. -/
@[simp]
theorem functor.snd
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    functor F G ⋙ π₂ F.toFunctor G.toFunctor =
      (PseudoPullback.snd F G).toFunctor := sorry

/-- The first component of a compared object is its first explicit pseudo-pullback
component. -/
@[simp]
theorem functor.obj.fst
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    ((functor F G).obj P).fst = PseudoPullback.fstObj P := sorry

/-- The second component of a compared object is its second explicit pseudo-pullback
component. -/
@[simp]
theorem functor.obj.snd
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    ((functor F G).obj P).snd = PseudoPullback.sndObj P := sorry

/-- The structural isomorphism of a compared object is the explicit objectwise
pseudo-pullback comparison. -/
@[simp]
theorem functor.obj.iso
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    ((functor F G).obj P).iso = PseudoPullback.comparisonIsoApp P := sorry

/-- The first component of a compared morphism is its first explicit pseudo-pullback
component. -/
@[simp]
theorem functor.map.fst
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    ((functor F G).map φ).fst = PseudoPullback.fstMap φ := sorry

/-- The second component of a compared morphism is its second explicit pseudo-pullback
component. -/
@[simp]
theorem functor.map.snd
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    ((functor F G).map φ).snd = PseudoPullback.sndMap φ := sorry

/-- Naturality of the objectwise base identification for the left projection.

Proof strategy: use the `IsHomLift.fac'` formula for the left component of an explicit
two-fibre-product morphism and cancel the two `eqToHom` transports. -/
theorem fstBaseIso.naturality
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    ((functor F G ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p)).map φ) ≫
          (PseudoPullback.fstBaseIso Q).hom =
      (PseudoPullback.fstBaseIso P).hom ≫
        (PseudoPullback F G).p.map φ := sorry

/-- The comparison is compatible with the left base projection. Its non-Prop components are the
canonical equality isomorphisms already stored by explicit pseudo-pullback objects. -/
noncomputable def fstBaseIso
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    functor F G ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≅
      (PseudoPullback F G).p :=
  NatIso.ofComponents (PseudoPullback.fstBaseIso)
    (fun φ =>
      fstBaseIso.naturality F G φ)

/-- The forward component of the left base-projection comparison is the stored first-fibre
base identification. -/
@[simp]
theorem fstBaseIso.hom.app
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    (Comparison.fstBaseIso F G).hom.app P =
      (PseudoPullback.fstBaseIso P).hom := sorry

/-- The inverse component of the left base-projection comparison is the inverse stored
first-fibre base identification. -/
@[simp]
theorem fstBaseIso.inv.app
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    (Comparison.fstBaseIso F G).inv.app P =
      (PseudoPullback.fstBaseIso P).inv := sorry

/-- Naturality of the objectwise base identification for the right projection.

Proof strategy: use the right-component `IsHomLift.fac'` formula for the deterministic comparison,
then cancel the equality transports. -/
theorem sndBaseIso.naturality
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    ((functor F G ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p)).map φ) ≫
          (PseudoPullback.sndBaseIso Q).hom =
      (PseudoPullback.sndBaseIso P).hom ≫
        (PseudoPullback F G).p.map φ := sorry

/-- The comparison is compatible with the right base projection. Its non-Prop components are the
canonical equality isomorphisms already stored by explicit pseudo-pullback objects. -/
noncomputable def sndBaseIso
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    functor F G ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≅
      (PseudoPullback F G).p :=
  NatIso.ofComponents (PseudoPullback.sndBaseIso)
    (fun φ =>
      sndBaseIso.naturality F G φ)

/-- The forward component of the right base-projection comparison is the stored second-fibre
base identification. -/
@[simp]
theorem sndBaseIso.hom.app
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    (Comparison.sndBaseIso F G).hom.app P =
      (PseudoPullback.sndBaseIso P).hom := sorry

/-- The inverse component of the right base-projection comparison is the inverse stored
second-fibre base identification. -/
@[simp]
theorem sndBaseIso.inv.app
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    (Comparison.sndBaseIso F G).inv.app P =
      (PseudoPullback.sndBaseIso P).inv := sorry

end BasedCategory.PseudoPullback.Comparison

end CategoryTheory
