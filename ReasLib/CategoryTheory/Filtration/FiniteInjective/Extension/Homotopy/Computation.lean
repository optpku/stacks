module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Homotopy.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor.Computation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for finite filtered extension homotopy comparisons

The declarations here specialize the generic bounded-below homotopy computation API to an
extension.  They intentionally expose only proposition-valued rewrite bridges; the functor and
comparison data remain owned by `Homotopy.Basic`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Homotopy

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

/-- The bounded-below homotopy functor agrees with the ambient homotopy functor after forgetting
the boundedness property. -/
@[stacks 05U1 "bounded-below homotopy inclusion comparison"]
noncomputable def compInclusionIso {T : A ⥤+ B} (E : Extension T) :
    E.homotopy ⋙
        (HomotopyCategory.plus (FilteredObject.Finite.category B)).ι ≅
      (HomotopyCategory.plus (category A)).ι ⋙
        E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.Homotopy.Plus.compInclusionIso E.functor.obj

/-- The forward component of the bounded-below inclusion comparison is the identity on the
ambient homotopy object. -/
@[simp, stacks 05U1 "bounded-below homotopy inclusion computation"]
theorem compInclusionIso_hom_app {T : A ⥤+ B} (E : Extension T)
    (K : HomotopyCategory.Plus (category A)) :
    (compInclusionIso E).hom.app K =
      𝟙 ((E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) := sorry

/-- The inverse component of the bounded-below inclusion comparison is the identity on the
ambient homotopy object. -/
@[simp, stacks 05U1 "bounded-below homotopy inclusion computation"]
theorem compInclusionIso_inv_app {T : A ⥤+ B} (E : Extension T)
    (K : HomotopyCategory.Plus (category A)) :
    (compInclusionIso E).inv.app K =
      𝟙 ((E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) := sorry

/-- The forward cochain-to-homotopy comparison has the generic ambient factorization component. -/
@[simp, stacks 05U1 "bounded-below cochain comparison computation"]
theorem quotientIso_hom_app_hom {T : A ⥤+ B} (E : Extension T)
    (K : CochainComplex.Plus (category A)) :
    ((quotientIso E).hom.app K).hom =
      (E.functor.obj.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K.obj := sorry

/-- The inverse cochain-to-homotopy comparison has the generic ambient factorization component. -/
@[simp, stacks 05U1 "bounded-below cochain comparison computation"]
theorem quotientIso_inv_app_hom {T : A ⥤+ B} (E : Extension T)
    (K : CochainComplex.Plus (category A)) :
    ((quotientIso E).inv.app K).hom =
      (E.functor.obj.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K.obj := sorry

/-- The forward component of the transported forgetful comparison is the composite of the
underlying comparison component and the canonical composition comparison. -/
@[simp, stacks 05U1 "bounded-below forgetful comparison computation"]
theorem forgetIso_hom_app {T : A ⥤+ B} (E : Extension T)
    (K : HomotopyCategory.Plus (category A)) :
    (forgetIso E).hom.app K =
      (Functor.mapHomotopyCategoryPlusCompIso E.forgetIso).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (forget A ⋙ T.obj))).inv.app K := sorry

/-- The inverse component of the transported forgetful comparison is the reverse composite of
the canonical composition comparison and the underlying comparison inverse. -/
@[simp, stacks 05U1 "bounded-below forgetful comparison computation"]
theorem forgetIso_inv_app {T : A ⥤+ B} (E : Extension T)
    (K : HomotopyCategory.Plus (category A)) :
    (forgetIso E).inv.app K =
      (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (forget A ⋙ T.obj))).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso E.forgetIso).inv.app K := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Homotopy
