/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Presheaf

/-!
# Additive fppf Picard sheaf before representability

This is the canonical additive sheafification of the raw line-bundle classes.
The quotient presentation and its comparison are in `Relative.Quotient.Fppf`.
The unit and universal property below use this same concrete plus-plus model,
so no equality with a separately chosen left adjoint is asserted.
-/

@[expose] public section

open CategoryTheory
noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

/-- The group-valued fppf sheaf of raw Picard classes. -/
noncomputable def additiveFppfSheaf {S : Scheme.{u}} (X : Over S) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (plusPlusSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (groupPresheaf X)

/-- The canonical map from line-bundle classes to the additive fppf sheaf. -/
noncomputable def toAdditiveFppfSheaf {S : Scheme.{u}} (X : Over S) :
    groupPresheaf X ⟶ (additiveFppfSheaf X).obj :=
  (Scheme.fppfTopology.over S).toSheafify (groupPresheaf X)

/-- Maps from the Picard sheaf to an additive sheaf are determined by raw classes. -/
noncomputable def additiveFppfSheafHomEquiv {S : Scheme.{u}} (X : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    (additiveFppfSheaf X ⟶ F) ≃ (groupPresheaf X ⟶ F.obj) :=
  (plusPlusAdjunction (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).homEquiv
    (groupPresheaf X) F

/-- The universal property restricts a sheaf morphism along the canonical unit. -/
@[simp]
theorem additiveFppfSheafHomEquiv_apply {S : Scheme.{u}} (X : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (g : additiveFppfSheaf X ⟶ F) :
    additiveFppfSheafHomEquiv X F g = toAdditiveFppfSheaf X ≫ g.hom := rfl

end AlgebraicGeometry.RelativePicard
