/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetry of `Tor`

@stack 00M3

This leaf supplies the comparison between the two derived `Tor` conventions in a braided
monoidal abelian category.  Mathlib defines `Tor` and `Tor'` separately; the braiding gives the
canonical comparison needed by homological applications.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory BraidedCategory

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]

/-- The fixed-left-variable form of the braided `Tor` symmetry. -/
@[stacks 00M3 "symmetry of Tor"]
noncomputable def torFlipLeftIso (i : ℕ) (M : C) :
    ((Tor C i).obj M) ≅ ((Functor.flip (Tor' C i)).obj M) where
  hom := NatTrans.leftDerived (tensorLeftIsoTensorRight M).hom i
  inv := NatTrans.leftDerived (tensorLeftIsoTensorRight M).inv i
  hom_inv_id := by
    dsimp only [Tor, Tor', Functor.flip]
    rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id, NatTrans.leftDerived_id]
  inv_hom_id := by
    dsimp only [Tor, Tor', Functor.flip]
    rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id, NatTrans.leftDerived_id]

/-- The canonical symmetry `Tor_i(M, N) ≅ Tor_i(N, M)` induced by the braiding. -/
@[stacks 00M3 "symmetry of Tor"]
noncomputable def torFlipIso (i : ℕ) : Tor C i ≅ Functor.flip (Tor' C i) where
  hom :=
    { app := fun M ↦ (torFlipLeftIso C i M).hom
      naturality := by
        intro X Y f
        dsimp only [Tor, Tor', Functor.flip, torFlipLeftIso]
        change NatTrans.leftDerived ((tensoringLeft C).map f) i ≫
            NatTrans.leftDerived (tensorLeftIsoTensorRight Y).hom i =
          NatTrans.leftDerived (tensorLeftIsoTensorRight X).hom i ≫
            NatTrans.leftDerived ((tensoringRight C).map f) i
        rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp]
        congr 1
        ext N
        exact braiding_naturality_left f N }
  inv :=
    { app := fun M ↦ (torFlipLeftIso C i M).inv
      naturality := by
        intro X Y f
        dsimp only [Tor, Tor', Functor.flip, torFlipLeftIso]
        change NatTrans.leftDerived ((tensoringRight C).map f) i ≫
            NatTrans.leftDerived (tensorLeftIsoTensorRight Y).inv i =
          NatTrans.leftDerived (tensorLeftIsoTensorRight X).inv i ≫
            NatTrans.leftDerived ((tensoringLeft C).map f) i
        rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp]
        congr 1
        ext N
        exact braiding_inv_naturality_right N f }
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    exact (torFlipLeftIso C i M).hom_inv_id
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    exact (torFlipLeftIso C i M).inv_hom_id

/-- The fixed-right-variable form of `torFlipIso`, comparing the public `Tor` convention
with the convention derived in the first variable. -/
@[stacks 00M3 "symmetry of Tor"]
noncomputable def torFlipRightIso (i : ℕ) (M : C) :
    ((Tor C i).flip.obj M) ≅ ((Tor' C i).obj M) where
  hom :=
    { app := fun X ↦ (((torFlipIso C i).hom.app X).app M)
      naturality := by
        intro X Y f
        exact congrArg (fun α ↦ α.app M) ((torFlipIso C i).hom.naturality f) }
  inv :=
    { app := fun X ↦ (((torFlipIso C i).inv.app X).app M)
      naturality := by
        intro X Y f
        exact congrArg (fun α ↦ α.app M) ((torFlipIso C i).inv.naturality f) }
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    exact (torFlipIso C i).hom_inv_id_app_app X M
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    exact (torFlipIso C i).inv_hom_id_app_app X M

end CategoryTheory
