module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Homotopy.Computation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of finite filtered extension homotopy comparisons

These are the ordinary naturality equations of the comparison isomorphisms, stated at the
cochain and bounded-homotopy levels.  They avoid forcing downstream proofs to unfold the
composition used to transport `Extension.forgetIso`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Homotopy

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

/-- Forward naturality of the cochain-to-homotopy comparison for an extension. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below cochain comparison naturality"]
theorem quotientIso_hom_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    (E.cochain ⋙
          HomotopyCategory.Plus.quotient (FilteredObject.Finite.category B)).map f ≫
        (quotientIso E).hom.app L =
      (quotientIso E).hom.app K ≫
        (HomotopyCategory.Plus.quotient (category A) ⋙ E.homotopy).map f := sorry

/-- Inverse naturality of the cochain-to-homotopy comparison for an extension. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below cochain comparison naturality"]
theorem quotientIso_inv_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    (HomotopyCategory.Plus.quotient (category A) ⋙ E.homotopy).map f ≫
        (quotientIso E).inv.app L =
      (quotientIso E).inv.app K ≫
        (E.cochain ⋙
          HomotopyCategory.Plus.quotient (FilteredObject.Finite.category B)).map f := sorry

/-- Forward naturality of the bounded-below inclusion comparison for an extension. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below homotopy inclusion naturality"]
theorem compInclusionIso_hom_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    (E.homotopy ⋙ (HomotopyCategory.plus (FilteredObject.Finite.category B)).ι).map f ≫
        (compInclusionIso E).hom.app L =
      (compInclusionIso E).hom.app K ≫
        ((HomotopyCategory.plus (category A)).ι ⋙
          E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ)).map f := sorry

/-- Inverse naturality of the bounded-below inclusion comparison for an extension. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below homotopy inclusion naturality"]
theorem compInclusionIso_inv_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    ((HomotopyCategory.plus (category A)).ι ⋙
          E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ)).map f ≫
        (compInclusionIso E).inv.app L =
      (compInclusionIso E).inv.app K ≫
        (E.homotopy ⋙ (HomotopyCategory.plus (FilteredObject.Finite.category B)).ι).map f := sorry

/-- Forward naturality of the transported forgetful comparison for an extension. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below forgetful comparison naturality"]
theorem forgetIso_hom_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    (E.homotopy ⋙
          (FilteredObject.Finite.Forget.functor B).mapHomotopyCategoryPlus).map f ≫
        (forgetIso E).hom.app L =
      (forgetIso E).hom.app K ≫
        ((forget A).mapHomotopyCategoryPlus ⋙ T.obj.mapHomotopyCategoryPlus).map f := sorry

/-- Inverse naturality of the transported forgetful comparison for an extension. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below forgetful comparison naturality"]
theorem forgetIso_inv_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    ((forget A).mapHomotopyCategoryPlus ⋙ T.obj.mapHomotopyCategoryPlus).map f ≫
        (forgetIso E).inv.app L =
      (forgetIso E).inv.app K ≫
        (E.homotopy ⋙
          (FilteredObject.Finite.Forget.functor B).mapHomotopyCategoryPlus).map f := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Homotopy
