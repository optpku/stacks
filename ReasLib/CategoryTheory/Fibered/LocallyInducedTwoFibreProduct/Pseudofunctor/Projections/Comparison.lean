/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection comparisons for locally induced two-fibre products

This leaf specializes the existing map projection comparisons to bundled selected cospans and
exposes their forward and inverse cells without duplicating the ambient computation API owned
by `map.fstIso` and `map.sndIso`.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [Projections.Has (P := P) (Q := Q)]
variable [Q.IsClosedUnderIsomorphisms]
variable [Projections.IsDetected (P := P) (Q := Q)]

/-- The first-projection comparison for the bundled locally induced two-fibre-product action. -/
@[stacks 02XQ "first projection of a locally induced two-fibre-product pseudofunctor"]
def pseudofunctor.fstIso
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor P Q).map ψ ≫ fst T.fst T.snd ≅
      fst S.fst S.snd ≫ Bicategory.Cospan.Hom.left ψ :=
  CategoryTheory.LocallyInduced.TwoFibreProduct.map.fstIso
    (Bicategory.Cospan.Hom.toCospanTransform ψ)

/-- The bundled first-projection comparison is the comparison already owned by the explicit
locally induced map. -/
@[simp]
theorem pseudofunctor.fstIso_eq
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    pseudofunctor.fstIso ψ =
      CategoryTheory.LocallyInduced.TwoFibreProduct.map.fstIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The forward bundled first-projection comparison is the forward comparison of the explicit
locally induced map. -/
@[simp]
theorem pseudofunctor.fstIso.hom
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor.fstIso ψ).hom =
      (CategoryTheory.LocallyInduced.TwoFibreProduct.map.fstIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).hom := sorry

/-- The inverse bundled first-projection comparison is the inverse comparison of the explicit
locally induced map. -/
@[simp]
theorem pseudofunctor.fstIso.inv
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor.fstIso ψ).inv =
      (CategoryTheory.LocallyInduced.TwoFibreProduct.map.fstIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).inv := sorry

/-- The second-projection comparison for the bundled locally induced two-fibre-product action. -/
@[stacks 02XQ "second projection of a locally induced two-fibre-product pseudofunctor"]
def pseudofunctor.sndIso
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor P Q).map ψ ≫ snd T.fst T.snd ≅
      snd S.fst S.snd ≫ Bicategory.Cospan.Hom.right ψ :=
  CategoryTheory.LocallyInduced.TwoFibreProduct.map.sndIso
    (Bicategory.Cospan.Hom.toCospanTransform ψ)

/-- The bundled second-projection comparison is the comparison already owned by the explicit
locally induced map. -/
@[simp]
theorem pseudofunctor.sndIso_eq
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    pseudofunctor.sndIso ψ =
      CategoryTheory.LocallyInduced.TwoFibreProduct.map.sndIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The forward bundled second-projection comparison is the forward comparison of the explicit
locally induced map. -/
@[simp]
theorem pseudofunctor.sndIso.hom
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor.sndIso ψ).hom =
      (CategoryTheory.LocallyInduced.TwoFibreProduct.map.sndIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).hom := sorry

/-- The inverse bundled second-projection comparison is the inverse comparison of the explicit
locally induced map. -/
@[simp]
theorem pseudofunctor.sndIso.inv
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor.sndIso ψ).inv =
      (CategoryTheory.LocallyInduced.TwoFibreProduct.map.sndIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)).inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
