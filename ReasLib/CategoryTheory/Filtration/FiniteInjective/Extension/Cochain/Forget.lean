module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Cochain.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful Comparison for Cochain Extensions

This leaf transports an extension's forgetful comparison to bounded-below cochain complexes and
provides the component and naturality equations used by applications.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Cochain

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

/-- The forgetful comparison of a filtered extension, transported to bounded-below cochain
complexes. -/
@[stacks 05U1 "bounded-below cochain forgetful comparison"]
noncomputable def forgetIso {T : A ⥤+ B} (E : Extension T) :
    E.cochain ⋙
        (FilteredObject.Finite.Forget.functor B).mapCochainComplexPlus ≅
      (forget A).mapCochainComplexPlus ⋙ T.obj.mapCochainComplexPlus :=
  Functor.Cochain.Plus.compIso E.forgetIso ≪≫
    (Functor.Cochain.Plus.compIso (Iso.refl (forget A ⋙ T.obj))).symm

/-- The forward component of the bounded-below cochain forgetful comparison. -/
@[simp, stacks 05U1 "bounded-below cochain forgetful comparison computation"]
theorem forgetIso_hom_app {T : A ⥤+ B} (E : Extension T)
    (K : CochainComplex.Plus (category A)) :
    (forgetIso E).hom.app K =
      (Functor.Cochain.Plus.compIso E.forgetIso).hom.app K ≫
        (Functor.Cochain.Plus.compIso (Iso.refl (forget A ⋙ T.obj))).inv.app K := sorry

/-- The inverse component of the bounded-below cochain forgetful comparison. -/
@[simp, stacks 05U1 "bounded-below cochain forgetful comparison computation"]
theorem forgetIso_inv_app {T : A ⥤+ B} (E : Extension T)
    (K : CochainComplex.Plus (category A)) :
    (forgetIso E).inv.app K =
      (Functor.Cochain.Plus.compIso (Iso.refl (forget A ⋙ T.obj))).hom.app K ≫
        (Functor.Cochain.Plus.compIso E.forgetIso).inv.app K := sorry

/-- Forward naturality of the bounded-below cochain forgetful comparison. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below cochain forgetful comparison naturality"]
theorem forgetIso_hom_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    (E.cochain ⋙
          (FilteredObject.Finite.Forget.functor B).mapCochainComplexPlus).map f ≫
        (forgetIso E).hom.app L =
      (forgetIso E).hom.app K ≫
        ((forget A).mapCochainComplexPlus ⋙ T.obj.mapCochainComplexPlus).map f := sorry

/-- Inverse naturality of the bounded-below cochain forgetful comparison. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below cochain forgetful comparison naturality"]
theorem forgetIso_inv_naturality {T : A ⥤+ B} (E : Extension T)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    ((forget A).mapCochainComplexPlus ⋙ T.obj.mapCochainComplexPlus).map f ≫
        (forgetIso E).inv.app L =
      (forgetIso E).inv.app K ≫
        (E.cochain ⋙
          (FilteredObject.Finite.Forget.functor B).mapCochainComplexPlus).map f := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Cochain
