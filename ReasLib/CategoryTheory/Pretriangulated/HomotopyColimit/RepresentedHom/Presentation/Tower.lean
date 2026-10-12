/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Tower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Contravariance of represented Hom towers

A morphism of sequential diagrams acts contravariantly on represented Hom towers. Diagram
isomorphisms induce tower isomorphisms with explicit forward and inverse morphisms.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- Precomposition with a morphism of sequential diagrams gives a morphism of represented
Hom towers in the reverse direction. -/
@[stacks 0CQX]
def towerPrecomp {K L : ℕ ⥤ D} (α : K ⟶ L) (Z : D) :
    tower L Z ⟶ tower K Z :=
  Functor.whiskerRight (NatTrans.op α) (preadditiveYoneda.obj Z)

/-- A component of `towerPrecomp` is represented Hom applied to the corresponding diagram
morphism. -/
@[simp]
theorem towerPrecomp_app {K L : ℕ ⥤ D} (α : K ⟶ L) (Z : D) (n : ℕ) :
    (towerPrecomp α Z).app (op n) =
      (preadditiveYoneda.obj Z).map (α.app n).op := sorry

/-- On elements, `towerPrecomp` acts by precomposition with the stage morphism. -/
@[simp]
theorem towerPrecomp_app_apply {K L : ℕ ⥤ D} (α : K ⟶ L) (Z : D)
    (n : ℕ) (f : L.obj n ⟶ Z) :
    (towerPrecomp α Z).app (op n) f = α.app n ≫ f := sorry

/-- Precomposition by the identity diagram morphism is the identity tower morphism. -/
@[simp]
theorem towerPrecomp_id (K : ℕ ⥤ D) (Z : D) :
    towerPrecomp (𝟙 K) Z = 𝟙 (tower K Z) := sorry

/-- Precomposition reverses composition of diagram morphisms. -/
@[simp]
theorem towerPrecomp_comp {K L M : ℕ ⥤ D} (α : K ⟶ L) (β : L ⟶ M) (Z : D) :
    towerPrecomp (α ≫ β) Z = towerPrecomp β Z ≫ towerPrecomp α Z := sorry

/-- A diagram isomorphism induces the contravariant isomorphism of represented Hom towers. -/
@[stacks 0CQX]
def towerPrecompIso {K L : ℕ ⥤ D} (e : K ≅ L) (Z : D) :
    tower L Z ≅ tower K Z :=
  Functor.isoWhiskerRight (NatIso.op e) (preadditiveYoneda.obj Z)

/-- The forward morphism of `towerPrecompIso` is precomposition by the forward diagram
morphism. -/
@[simp]
theorem towerPrecompIso_hom {K L : ℕ ⥤ D} (e : K ≅ L) (Z : D) :
    (towerPrecompIso e Z).hom = towerPrecomp e.hom Z := sorry

/-- The inverse morphism of `towerPrecompIso` is precomposition by the inverse diagram
morphism. -/
@[simp]
theorem towerPrecompIso_inv {K L : ℕ ⥤ D} (e : K ≅ L) (Z : D) :
    (towerPrecompIso e Z).inv = towerPrecomp e.inv Z := sorry

section Shift

variable [HasShift D ℤ]

/-- Precomposition with a diagram morphism gives a morphism of shifted represented Hom towers
in the reverse direction. -/
@[stacks 0CQX]
def shiftedTowerPrecomp {K L : ℕ ⥤ D} (α : K ⟶ L) (Z : D) :
    shiftedTower L Z ⟶ shiftedTower K Z :=
  Functor.whiskerRight (NatTrans.op α) (preadditiveYoneda.obj (Z⟦(-1 : ℤ)⟧))

/-- A component of `shiftedTowerPrecomp` is represented Hom into the shifted target applied to
the corresponding diagram morphism. -/
@[simp]
theorem shiftedTowerPrecomp_app {K L : ℕ ⥤ D} (α : K ⟶ L) (Z : D) (n : ℕ) :
    (shiftedTowerPrecomp α Z).app (op n) =
      (preadditiveYoneda.obj (Z⟦(-1 : ℤ)⟧)).map (α.app n).op := sorry

/-- On elements, `shiftedTowerPrecomp` acts by precomposition with the stage morphism. -/
@[simp]
theorem shiftedTowerPrecomp_app_apply {K L : ℕ ⥤ D} (α : K ⟶ L) (Z : D)
    (n : ℕ) (f : L.obj n ⟶ Z⟦(-1 : ℤ)⟧) :
    (shiftedTowerPrecomp α Z).app (op n) f = α.app n ≫ f := sorry

/-- Shifted-tower precomposition by an identity is the identity. -/
@[simp]
theorem shiftedTowerPrecomp_id (K : ℕ ⥤ D) (Z : D) :
    shiftedTowerPrecomp (𝟙 K) Z = 𝟙 (shiftedTower K Z) := sorry

/-- Shifted-tower precomposition reverses composition of diagram morphisms. -/
@[simp]
theorem shiftedTowerPrecomp_comp {K L M : ℕ ⥤ D}
    (α : K ⟶ L) (β : L ⟶ M) (Z : D) :
    shiftedTowerPrecomp (α ≫ β) Z =
      shiftedTowerPrecomp β Z ≫ shiftedTowerPrecomp α Z := sorry

/-- A diagram isomorphism induces the contravariant isomorphism of shifted represented Hom
towers. -/
@[stacks 0CQX]
def shiftedTowerPrecompIso {K L : ℕ ⥤ D} (e : K ≅ L) (Z : D) :
    shiftedTower L Z ≅ shiftedTower K Z :=
  Functor.isoWhiskerRight (NatIso.op e)
    (preadditiveYoneda.obj (Z⟦(-1 : ℤ)⟧))

/-- The forward morphism of `shiftedTowerPrecompIso` is precomposition by the forward diagram
morphism. -/
@[simp]
theorem shiftedTowerPrecompIso_hom {K L : ℕ ⥤ D} (e : K ≅ L) (Z : D) :
    (shiftedTowerPrecompIso e Z).hom = shiftedTowerPrecomp e.hom Z := sorry

/-- The inverse morphism of `shiftedTowerPrecompIso` is precomposition by the inverse diagram
morphism. -/
@[simp]
theorem shiftedTowerPrecompIso_inv {K L : ℕ ⥤ D} (e : K ≅ L) (Z : D) :
    (shiftedTowerPrecompIso e Z).inv = shiftedTowerPrecomp e.inv Z := sorry

end Shift

end CategoryTheory.HomotopyColimit.RepresentedHom

end
