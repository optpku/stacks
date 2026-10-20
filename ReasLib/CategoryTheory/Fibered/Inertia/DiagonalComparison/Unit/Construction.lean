module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Inverse.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison unit construction

This module owns the explicit components and packaged based natural isomorphism
forming the unit for the diagonal-comparison inverse.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The identity arrow intertwines a relative-inertia automorphism with the automorphism
recovered after applying the comparison and its explicit inverse. -/
@[stacks 034H "diagonal-comparison unit component compatibility"]
theorem RelativeInertia.diagonalComparison.unitIso.hom.naturality (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    A.aut.hom ≫ 𝟙 A.obj =
      𝟙 A.obj ≫
        ((RelativeInertia.diagonalComparison.inverse F).obj
          ((RelativeInertia.diagonalComparison F).obj A)).aut.hom := sorry

/-- The component isomorphism of the unit for the explicit relative-inertia comparison
inverse. It reuses the generic relative-inertia isomorphism constructor, so the inverse
intertwining equation and inverse laws are not rebuilt locally. -/
@[stacks 034H "diagonal-comparison unit component"]
noncomputable def RelativeInertia.diagonalComparison.unitIso.app (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    A ≅
      (RelativeInertia.diagonalComparison.inverse F).obj
        ((RelativeInertia.diagonalComparison F).obj A) :=
  CategoryTheory.RelativeInertia.isoMk F.toFunctor (Iso.refl _)
    (RelativeInertia.diagonalComparison.unitIso.hom.naturality F A)

/-- The unit components for the explicit comparison inverse are natural in relative-inertia
morphisms. -/
@[stacks 034H "diagonal-comparison unit naturality"]
theorem RelativeInertia.diagonalComparison.unitIso.naturality (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (φ : A ⟶ B) :
    φ ≫ (RelativeInertia.diagonalComparison.unitIso.app F B).hom =
      (RelativeInertia.diagonalComparison.unitIso.app F A).hom ≫
        (RelativeInertia.diagonalComparison F ⋙
          RelativeInertia.diagonalComparison.inverse F).map φ := sorry

/-- The inverse comparison-unit component is natural in relative-inertia morphisms. -/
@[reassoc, stacks 034H "diagonal-comparison inverse unit naturality"]
theorem RelativeInertia.diagonalComparison.unitIso.invNaturality (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (φ : A ⟶ B) :
    (RelativeInertia.diagonalComparison.unitIso.app F A).inv ≫ φ =
      (RelativeInertia.diagonalComparison F ⋙
        RelativeInertia.diagonalComparison.inverse F).map φ ≫
        (RelativeInertia.diagonalComparison.unitIso.app F B).inv := sorry

/-- The ordinary natural isomorphism underlying the unit for the explicit comparison inverse. -/
@[stacks 034H "diagonal-comparison unit underlying natural isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.unitIso.toNatIso (F : X ⥤ᵇ Y) :
    (𝟭 (BasedCategory.ofFunctor
      (CategoryTheory.RelativeInertia.projection F.toFunctor X.p))).toFunctor ≅
      (RelativeInertia.diagonalComparison F ⋙
        RelativeInertia.diagonalComparison.inverse F).toFunctor :=
  NatIso.ofComponents
    (RelativeInertia.diagonalComparison.unitIso.app F)
    (fun φ ↦ RelativeInertia.diagonalComparison.unitIso.naturality F φ)

/-- Every forward unit component is vertical over the identity of its base object. -/
@[stacks 034H "diagonal-comparison unit forward hom-lift"]
theorem RelativeInertia.diagonalComparison.unitIso.app.hom.isHomLift (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p).IsHomLift
      (𝟙 ((CategoryTheory.RelativeInertia.projection F.toFunctor X.p).obj A))
      (RelativeInertia.diagonalComparison.unitIso.app F A).hom := sorry

/-- Every inverse comparison-unit component is vertical over the identity of its base object. -/
@[stacks 034H "diagonal-comparison unit inverse hom-lift"]
theorem RelativeInertia.diagonalComparison.unitIso.app.inv.isHomLift (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p).IsHomLift
      (𝟙 ((CategoryTheory.RelativeInertia.projection F.toFunctor X.p).obj A))
      (RelativeInertia.diagonalComparison.unitIso.app F A).inv := sorry

/-- The based natural isomorphism serving as the unit for the explicit relative-inertia
comparison inverse. -/
@[stacks 034H "relative-inertia diagonal-comparison unit"]
noncomputable def RelativeInertia.diagonalComparison.unitIso (F : X ⥤ᵇ Y) :
    𝟭 (BasedCategory.ofFunctor
        (CategoryTheory.RelativeInertia.projection F.toFunctor X.p)) ≅
      RelativeInertia.diagonalComparison F ⋙
        RelativeInertia.diagonalComparison.inverse F :=
  BasedNatIso.mkNatIso
    (RelativeInertia.diagonalComparison.unitIso.toNatIso F)
    (RelativeInertia.diagonalComparison.unitIso.app.hom.isHomLift F)

end BasedFunctor

end CategoryTheory
