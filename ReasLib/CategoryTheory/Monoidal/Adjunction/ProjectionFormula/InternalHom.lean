/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas and internal Hom

A left projection formula for a monoidal adjunction makes the canonical lax-monoidal
internal-Hom comparison of its right adjoint invertible.  This file constructs the inverse
morphism explicitly before packaging the comparison as an isomorphism.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Adjunction.LeftProjectionFormulaMap

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [L.OplaxMonoidal] [R.LaxMonoidal] [adj.IsMonoidal]

/-- The explicit inverse candidate for the lax-monoidal internal-Hom comparison, obtained by
transposing evaluation across the adjunction and the left projection formula. -/
@[stacks 0E8H "comparison inverse"]
noncomputable def comparisonInv (X Y : D)
    [Closed X] [Closed (R.obj X)]
    [IsIso (adj.leftProjectionFormulaMap X
      ((ihom (R.obj X)).obj (R.obj Y)))] :
    (ihom (R.obj X)).obj (R.obj Y) ⟶ R.obj ((ihom X).obj Y) :=
  adj.homEquiv _ _
    (curry
      ((adj.leftProjectionFormulaMapIso X
          ((ihom (R.obj X)).obj (R.obj Y))).hom ≫
        L.map ((ihom.ev (R.obj X)).app (R.obj Y)) ≫
        adj.counit.app Y))

/-- The canonical internal-Hom comparison followed by its projection-formula inverse is the
identity. -/
theorem comparison_comp_inv (X Y : D)
    [Closed X] [Closed (R.obj X)]
    [IsIso (adj.leftProjectionFormulaMap X
      ((ihom (R.obj X)).obj (R.obj Y)))] :
    Functor.LaxMonoidal.InternalHom.comparison R X Y ≫
        comparisonInv adj X Y = 𝟙 _ := sorry

/-- The projection-formula inverse followed by the canonical internal-Hom comparison is the
identity. -/
theorem inv_comp_comparison (X Y : D)
    [Closed X] [Closed (R.obj X)]
    [IsIso (adj.leftProjectionFormulaMap X
      ((ihom (R.obj X)).obj (R.obj Y)))] :
    comparisonInv adj X Y ≫
        Functor.LaxMonoidal.InternalHom.comparison R X Y = 𝟙 _ := sorry

/-- The canonical internal-Hom comparison, bundled with its explicit projection-formula
inverse. -/
@[stacks 0E8H "comparison isomorphism"]
noncomputable def comparisonIso (X Y : D)
    [Closed X] [Closed (R.obj X)]
    [IsIso (adj.leftProjectionFormulaMap X
      ((ihom (R.obj X)).obj (R.obj Y)))] :
    R.obj ((ihom X).obj Y) ≅ (ihom (R.obj X)).obj (R.obj Y) where
  hom := Functor.LaxMonoidal.InternalHom.comparison R X Y
  inv := comparisonInv adj X Y
  hom_inv_id := comparison_comp_inv adj X Y
  inv_hom_id := inv_comp_comparison adj X Y

/-- A componentwise left projection formula makes the canonical internal-Hom comparison
invertible. -/
@[stacks 0E8H "comparison invertibility"]
theorem comparison_isIso (X Y : D)
    [Closed X] [Closed (R.obj X)]
    [IsIso (adj.leftProjectionFormulaMap X
      ((ihom (R.obj X)).obj (R.obj Y)))] :
    IsIso (Functor.LaxMonoidal.InternalHom.comparison R X Y) := sorry

/-- A left projection formula makes the right adjoint preserve every internal Hom for which the
source and its image are closed.  This is a theorem rather than a global instance because the
right adjoint does not determine its chosen left adjoint. -/
@[stacks 0E8H "preservation from projection formula"]
theorem preservesInternalHom [adj.LeftProjectionFormulaMap] :
    Functor.LaxMonoidal.PreservesInternalHom R := sorry

-- Both morphism fields of `comparisonIso` are explicit above.  Its `sorryAx` is confined to the
-- two equality proof fields supplied by `comparison_comp_inv` and `inv_comp_comparison`.

end CategoryTheory.Adjunction.LeftProjectionFormulaMap
