/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical symmetry `Tor_i(M, N) ≅ Tor_i(N, M)` induced by the braiding. -/
@[stacks 00M3 "symmetry of Tor"]
noncomputable def torFlipIso (i : ℕ) : Tor C i ≅ Functor.flip (Tor' C i) where
  hom :=
    { app := fun M ↦ (torFlipLeftIso C i M).hom
      naturality := sorry }
  inv :=
    { app := fun M ↦ (torFlipLeftIso C i M).inv
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The fixed-right-variable form of `torFlipIso`, comparing the public `Tor` convention
with the convention derived in the first variable. -/
@[stacks 00M3 "symmetry of Tor"]
noncomputable def torFlipRightIso (i : ℕ) (M : C) :
    ((Tor C i).flip.obj M) ≅ ((Tor' C i).obj M) where
  hom :=
    { app := fun X ↦ (((torFlipIso C i).hom.app X).app M)
      naturality := sorry }
  inv :=
    { app := fun X ↦ (((torFlipIso C i).inv.app X).app M)
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

end CategoryTheory
