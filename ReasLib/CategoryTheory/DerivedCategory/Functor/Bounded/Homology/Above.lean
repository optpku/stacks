/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization.Computation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Pasting

/-!
# Homology of termwise maps on bounded-above complexes

For an additive functor, ordinary homology after mapping a bounded-above complex agrees naturally
with homology after passing through the bounded-above homotopy and derived categories.  This does
not require a derived functor of the additive functor.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Minus.Homology

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]

/-- Ordinary homology of a termwise mapped bounded-above complex agrees with homology after
passing through the bounded-above derived category. -/
@[stacks 015H "homology after mapping a bounded-above complex"]
noncomputable def homologyIso (L : CochainComplex.Minus A) (n : ℤ) :
    ((CochainComplex.Minus.ι B).obj ((Functor.Cochain.Minus.map F).obj L)).homology n ≅
      (DerivedCategory.Minus.homologyFunctor B n).obj
        (F.toBoundedAboveDerived.obj ((HomotopyCategory.Minus.quotient A).obj L)) :=
  (DerivedCategory.homologyFunctorFactors B n).symm.app
      ((CochainComplex.Minus.ι B).obj ((Functor.Cochain.Minus.map F).obj L)) ≪≫
    (DerivedCategory.homologyFunctor B n).mapIso
      ((DerivedCategory.Minus.Qh.compInclusionIso B).symm.app
        ((HomotopyCategory.Minus.quotient B).obj
          ((Functor.Cochain.Minus.map F).obj L))) ≪≫
    (DerivedCategory.Minus.homologyFunctor B n).mapIso
      ((DerivedCategory.Minus.Qh B).mapIso
        ((Functor.Homotopy.Minus.quotientIso F).app L))

namespace homologyIso

/-- The forward comparison is the canonical transport through the ordinary derived category,
the bounded inclusion, and the homotopy quotient comparison. -/
@[simp]
theorem hom (L : CochainComplex.Minus A) (n : ℤ) :
    (homologyIso F L n).hom =
      (DerivedCategory.homologyFunctorFactors B n).inv.app
          ((CochainComplex.Minus.ι B).obj ((Functor.Cochain.Minus.map F).obj L)) ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Minus.Qh.compInclusionIso B).inv.app
            ((HomotopyCategory.Minus.quotient B).obj
              ((Functor.Cochain.Minus.map F).obj L))) ≫
        (DerivedCategory.Minus.homologyFunctor B n).map
          ((DerivedCategory.Minus.Qh B).map
            ((Functor.Homotopy.Minus.quotientIso F).hom.app L)) := sorry

/-- The inverse comparison reverses the homotopy quotient, bounded inclusion, and ordinary
derived-category transports. -/
@[simp]
theorem inv (L : CochainComplex.Minus A) (n : ℤ) :
    (homologyIso F L n).inv =
      (DerivedCategory.Minus.homologyFunctor B n).map
          ((DerivedCategory.Minus.Qh B).map
            ((Functor.Homotopy.Minus.quotientIso F).inv.app L)) ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Minus.Qh.compInclusionIso B).hom.app
            ((HomotopyCategory.Minus.quotient B).obj
              ((Functor.Cochain.Minus.map F).obj L))) ≫
        (DerivedCategory.homologyFunctorFactors B n).hom.app
          ((CochainComplex.Minus.ι B).obj ((Functor.Cochain.Minus.map F).obj L)) := sorry

/-- The bounded-above homology comparisons are natural in the source complex. -/
@[reassoc]
theorem hom_naturality {L M : CochainComplex.Minus A} (f : L ⟶ M) (n : ℤ) :
    (Functor.Cochain.Minus.map F ⋙ CochainComplex.Minus.ι B ⋙
          HomologicalComplex.homologyFunctor B (up ℤ) n).map f ≫
        (homologyIso F M n).hom =
      (homologyIso F L n).hom ≫
        (HomotopyCategory.Minus.quotient A ⋙ F.toBoundedAboveDerived ⋙
          DerivedCategory.Minus.homologyFunctor B n).map f := sorry

/-- The inverse bounded-above homology comparisons are natural in the source complex. -/
@[reassoc]
theorem inv_naturality {L M : CochainComplex.Minus A} (f : L ⟶ M) (n : ℤ) :
    (HomotopyCategory.Minus.quotient A ⋙ F.toBoundedAboveDerived ⋙
          DerivedCategory.Minus.homologyFunctor B n).map f ≫
        (homologyIso F M n).inv =
      (homologyIso F L n).inv ≫
        (Functor.Cochain.Minus.map F ⋙ CochainComplex.Minus.ι B ⋙
          HomologicalComplex.homologyFunctor B (up ℤ) n).map f := sorry

end homologyIso

/-- The homology comparisons assemble into a natural isomorphism on bounded-above complexes. -/
@[stacks 015H "natural homology comparison for bounded-above termwise maps"]
noncomputable def homologyFunctorIso (n : ℤ) :
    Functor.Cochain.Minus.map F ⋙ CochainComplex.Minus.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n ≅
      HomotopyCategory.Minus.quotient A ⋙ F.toBoundedAboveDerived ⋙
        DerivedCategory.Minus.homologyFunctor B n :=
  Functor.HomologyComparison.pasteIso
    ⟨Functor.Homotopy.Minus.quotientIso F⟩
    ⟨HomotopyCategory.Minus.quotientCompιIso B⟩
    ⟨DerivedCategory.Minus.Qh.compInclusionIso B⟩
    (DerivedCategory.quotientCompQhIso B)
    (DerivedCategory.homologyFunctorFactors B n)

namespace homologyFunctorIso

/-- The component of the natural bounded-above homology comparison is `homologyIso`. -/
@[simp]
theorem app (L : CochainComplex.Minus A) (n : ℤ) :
    (homologyFunctorIso F n).app L = homologyIso F L n := sorry

end homologyFunctorIso

end CategoryTheory.Functor.Homotopy.Minus.Homology
