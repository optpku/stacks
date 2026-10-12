/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Computations for target-hom postcomposition

This module exposes both the raw `LocallyDiscrete` fields and the base-facing
`mapIdOp`/`mapCompOp` formulas of `postcompose.pseudofunctor`. The latter hide
the opposite-category bookkeeping, so applications can work directly with
target `1`- and `2`-morphisms.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose.pseudofunctor

/-- The object action of target-hom postcomposition is postcomposition by the
underlying target `1`-morphism. -/
@[simp]
theorem obj
    (K : Pseudofunctor A C) (f : (X ⟶ Y)ᵒᵖ) :
    (postcompose.pseudofunctor K X Y).obj (LocallyDiscrete.mk f) =
      postcompose K f.unop := sorry

/-- The morphism action of target-hom postcomposition is the contravariant
strong transformation induced by the underlying target `2`-morphism. -/
@[simp]
theorem map
    (K : Pseudofunctor A C) {f g : (X ⟶ Y)ᵒᵖ} (η : f ⟶ g) :
    (postcompose.pseudofunctor K X Y).map η.toLoc =
      postcompose.cellStrongTrans K η.unop := sorry

/-- The identity comparison of target-hom postcomposition is the explicit
target-cell identity comparison. -/
@[simp]
theorem mapId
    (K : Pseudofunctor A C) (f : (X ⟶ Y)ᵒᵖ) :
    (postcompose.pseudofunctor K X Y).mapId
        (LocallyDiscrete.mk f) =
      postcompose.cellMapId K f.unop := sorry

/-- The composition comparison of target-hom postcomposition is the explicit
target-cell comparison with the two underlying cells in reversed order. -/
@[simp]
theorem mapComp
    (K : Pseudofunctor A C) {f g h : (X ⟶ Y)ᵒᵖ}
    (η : f ⟶ g) (θ : g ⟶ h) :
    (postcompose.pseudofunctor K X Y).mapComp η.toLoc θ.toLoc =
      postcompose.cellMapComp K θ.unop η.unop := sorry

/-! Base-facing computation formulas for the opposite locally discrete domain. -/

namespace base

/-- The object action, written for an underlying target `1`-morphism rather than
its opposite object. -/
@[simp]
theorem obj
    (K : Pseudofunctor A C) (f : X ⟶ Y) :
    (postcompose.pseudofunctor K X Y).obj (LocallyDiscrete.mk f.op) =
      postcompose K f := sorry

/-- The morphism action, written for an underlying target `2`-morphism. -/
@[simp]
theorem map
    (K : Pseudofunctor A C) {f g : X ⟶ Y} (η : f ⟶ g) :
    (postcompose.pseudofunctor K X Y).map η.op.toLoc =
      postcompose.cellStrongTrans K η := sorry

/-- The component of the base-facing target-cell action is the explicit
contravariant costructured-arrow component. -/
@[simp]
theorem map.app
    {f g : X ⟶ Y} (η : f ⟶ g) (S : ColaxCostructuredArrow K X) :
    ((postcompose.pseudofunctor K X Y).map η.op.toLoc).app S =
      postcompose.cellComponent η S := sorry

/-- The strong naturality of the base-facing target-cell action is the
explicit costructured-arrow naturality isomorphism. -/
@[simp]
theorem map.naturality
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ((postcompose.pseudofunctor K X Y).map η.op.toLoc).naturality u =
      postcompose.cellNaturality η u := sorry

/-- The base-facing identity comparison is the explicit target-cell identity
comparison. -/
@[simp]
theorem mapId
    (K : Pseudofunctor A C) (f : X ⟶ Y) :
    (postcompose.pseudofunctor K X Y).mapIdOp f =
      postcompose.cellMapId K f := sorry

/-- The base-facing composition comparison is the explicit comparison for the
reversed target-cell action. -/
@[simp]
theorem mapComp
    (K : Pseudofunctor A C) {f g h : X ⟶ Y}
    (η : f ⟶ g) (θ : g ⟶ h) :
    (postcompose.pseudofunctor K X Y).mapCompOp θ η =
      postcompose.cellMapComp K η θ := sorry

/-! Component and source-cell formulas for the base-facing comparisons. -/

/-- The forward component of the base-facing identity comparison is the
explicit target-cell identity component. -/
@[simp]
theorem mapId.hom.app
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ((postcompose.pseudofunctor K X Y).mapIdOp f).hom.as.app S =
      (postcompose.cellMapId.app f S).hom := sorry

/-- The inverse component of the base-facing identity comparison is the
inverse explicit target-cell identity component. -/
@[simp]
theorem mapId.inv.app
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ((postcompose.pseudofunctor K X Y).mapIdOp f).inv.as.app S =
      (postcompose.cellMapId.app f S).inv := sorry

/-- The source cell of a forward base-facing identity-comparison component is
the identity `2`-morphism. -/
@[simp]
theorem mapId.hom.app.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (((postcompose.pseudofunctor K X Y).mapIdOp f).hom.as.app S) =
      𝟙 (𝟙 S.left) := sorry

/-- The source cell of an inverse base-facing identity-comparison component is
the identity `2`-morphism. -/
@[simp]
theorem mapId.inv.app.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (((postcompose.pseudofunctor K X Y).mapIdOp f).inv.as.app S) =
      𝟙 (𝟙 S.left) := sorry

/-- The forward component of the base-facing composition comparison is the
explicit target-cell composition component. -/
@[simp]
theorem mapComp.hom.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ((postcompose.pseudofunctor K X Y).mapCompOp θ η).hom.as.app S =
      (postcompose.cellMapComp.app η θ S).hom := sorry

/-- The inverse component of the base-facing composition comparison is the
inverse explicit target-cell composition component. -/
@[simp]
theorem mapComp.inv.app
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ((postcompose.pseudofunctor K X Y).mapCompOp θ η).inv.as.app S =
      (postcompose.cellMapComp.app η θ S).inv := sorry

/-- The source cell of a forward base-facing composition-comparison component
is the inverse right-unitor cell on the unchanged source map. -/
@[simp]
theorem mapComp.hom.app.map₂
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (((postcompose.pseudofunctor K X Y).mapCompOp θ η).hom.as.app S) =
      (ρ_ (𝟙 S.left)).inv := sorry

/-- The source cell of an inverse base-facing composition-comparison component
is the right-unitor cell inverse to the chosen forward source comparison. -/
@[simp]
theorem mapComp.inv.app.map₂
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (((postcompose.pseudofunctor K X Y).mapCompOp θ η).inv.as.app S) =
      (ρ_ (𝟙 S.left)).hom := sorry

end base

end postcompose.pseudofunctor

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
