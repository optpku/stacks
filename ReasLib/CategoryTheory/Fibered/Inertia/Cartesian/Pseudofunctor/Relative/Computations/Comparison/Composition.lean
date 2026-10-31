/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.Action
import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Computations.Comparisons

/-!
# Composition comparison computations for fibred relative inertia
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- The composition comparison of fibred relative inertia is the canonical
lift of its based composition comparison. -/
@[simp]
theorem pseudofunctor.mapComp
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T) :
    (pseudofunctor C).mapComp f g =
      FiberedCategoryOver.BasedFunctorIso.lift
        ((basedPseudofunctor C).mapComp f g) := by
  rfl

/-- The forward fibred relative-inertia composition comparison forgets to
the underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapComp.hom.toBasedNatTrans
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapComp f g).hom =
      ((basedPseudofunctor C).mapComp f g).hom := by
  rfl

/-- The inverse fibred relative-inertia composition comparison forgets to
the underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapComp.inv.toBasedNatTrans
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapComp f g).inv =
      ((basedPseudofunctor C).mapComp f g).inv := by
  rfl

/-- The forward composition comparison component is the corresponding
component of the based relative-inertia pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T)
    (A : ((pseudofunctor C).obj R).total) :
    (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapComp f g).hom).app A =
      ((basedPseudofunctor C).mapComp f g).hom.toNatTrans.app A := by
  rfl

/-- The inverse composition comparison component is the corresponding
component of the based relative-inertia pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T)
    (A : ((pseudofunctor C).obj R).total) :
    (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapComp f g).inv).app A =
      ((basedPseudofunctor C).mapComp f g).inv.toNatTrans.app A := by
  rfl

/-- Every forward component of the packaged fibred relative-inertia composition comparison is
vertical over the identity base arrow. -/
theorem pseudofunctor.mapComp.hom.app.isHomLift
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T)
    (A : ((pseudofunctor C).obj R).total) :
    (FiberedCategoryOver.relativeInertia T.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia R.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapComp f g).hom).app A) := by
  exact (FiberedCategoryOver.toBasedNatTrans
    ((pseudofunctor C).mapComp f g).hom).isHomLift' A

/-- Every inverse component of the packaged fibred relative-inertia composition comparison is
vertical over the identity base arrow. -/
theorem pseudofunctor.mapComp.inv.app.isHomLift
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T)
    (A : ((pseudofunctor C).obj R).total) :
    (FiberedCategoryOver.relativeInertia T.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia R.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapComp f g).inv).app A) := by
  exact (FiberedCategoryOver.toBasedNatTrans
    ((pseudofunctor C).mapComp f g).inv).isHomLift' A

/-- The ambient arrow underlying a forward composition-comparison component
is an identity. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app.underlying
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T)
    (A : ((pseudofunctor C).obj R).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapComp f g).hom).app A) =
      𝟙 _ := by
  let X := (FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left g)).obj
    ((FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left f)).obj A.obj)
  change (Bicategory.PseudoComma.left₂
    ((toBased C).mapComp f g).hom).toNatTrans.app A.obj ≫ 𝟙 X = 𝟙 X
  rw [toBased.mapComp.hom.left, StrictPseudofunctor.mapComp_eq_eqToIso]
  change 𝟙 X ≫ 𝟙 X = 𝟙 X
  simp

/-- The ambient arrow underlying an inverse composition-comparison component
is an identity. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app.underlying
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : R ⟶ S) (g : S ⟶ T)
    (A : ((pseudofunctor C).obj R).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapComp f g).inv).app A) =
      𝟙 _ := by
  let X := (FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left g)).obj
    ((FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left f)).obj A.obj)
  change 𝟙 X ≫ (Bicategory.PseudoComma.left₂
    ((toBased C).mapComp f g).inv).toNatTrans.app A.obj = 𝟙 X
  rw [toBased.mapComp.inv.left, StrictPseudofunctor.mapComp_eq_eqToIso]
  change 𝟙 X ≫ 𝟙 X = 𝟙 X
  simp

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
