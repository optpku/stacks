module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback and postcomposition around a cartesian square

A cartesian square identifies pullback followed by postcomposition with
postcomposition followed by pullback between slice categories.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {S S' T T' : C}

/-- A cartesian square identifies the two pullback objects over its lower-left vertex. -/
def pullbackMapIsoApp
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) (U : Over S') :
    (Over.pullback f' ⋙ Over.map g').obj U ≅
      (Over.map g ⋙ Over.pullback f).obj U :=
  let inner : IsPullback
      (pullback.snd U.hom f') (pullback.fst U.hom f') f' U.hom :=
    (IsPullback.of_hasPullback U.hom f').flip
  let outer : IsPullback
      (pullback.snd U.hom f' ≫ g') (pullback.fst U.hom f') f (U.hom ≫ g) :=
    inner.paste_horiz sq
  let chosen : IsPullback
      (pullback.snd (U.hom ≫ g) f) (pullback.fst (U.hom ≫ g) f) f (U.hom ≫ g) :=
    (IsPullback.of_hasPullback (U.hom ≫ g) f).flip
  Over.isoMk (outer.isoIsPullback T U.left chosen)
    (outer.isoIsPullback_hom_fst T U.left chosen)

/-- The cartesian pullback-postcomposition identification is natural in the slice object. -/
theorem pullbackMapIso_naturality
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) {U V : Over S'} (φ : U ⟶ V) :
    (Over.pullback f' ⋙ Over.map g').map φ ≫ (pullbackMapIsoApp f g f' g' sq V).hom =
      (pullbackMapIsoApp f g f' g' sq U).hom ≫
        (Over.map g ⋙ Over.pullback f).map φ := sorry

/-- Pullback and postcomposition commute, up to natural isomorphism, around a cartesian square. -/
def pullbackMapIso
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    Over.pullback f' ⋙ Over.map g' ≅ Over.map g ⋙ Over.pullback f :=
  NatIso.ofComponents (pullbackMapIsoApp f g f' g' sq)
    (pullbackMapIso_naturality f g f' g' sq)

end CategoryTheory.Over
