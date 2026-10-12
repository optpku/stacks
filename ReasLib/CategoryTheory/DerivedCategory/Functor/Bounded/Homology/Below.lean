/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization.Computation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Pasting

/-!
# Homology of termwise maps on bounded-below complexes

For an additive functor, ordinary homology after mapping a bounded-below complex agrees naturally
with homology after passing through the bounded-below homotopy and derived categories.  This does
not require a derived functor of the additive functor.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Plus.Homology

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]

/-- Ordinary homology of a termwise mapped bounded-below complex agrees with homology after
passing through the bounded-below derived category. -/
@[stacks 015H "homology after mapping a bounded-below complex"]
noncomputable def homologyIso (L : CochainComplex.Plus A) (n : ℤ) :
    ((CochainComplex.Plus.ι B).obj (F.mapCochainComplexPlus.obj L)).homology n ≅
      (DerivedCategory.Plus.homologyFunctor B n).obj
        (F.toBoundedBelowDerived.obj ((HomotopyCategory.Plus.quotient A).obj L)) :=
  (DerivedCategory.homologyFunctorFactors B n).symm.app
      ((CochainComplex.Plus.ι B).obj (F.mapCochainComplexPlus.obj L)) ≪≫
    (DerivedCategory.homologyFunctor B n).mapIso
      ((DerivedCategory.Plus.Qh.compInclusionIso B).symm.app
        (F.mapCochainComplexPlus.obj L)) ≪≫
    (DerivedCategory.Plus.homologyFunctor B n).mapIso
      (DerivedCategory.Plus.Qh.mapIso
        ((Functor.Homotopy.Plus.quotientIso F).app L))

namespace homologyIso

/-- The forward comparison is the canonical transport through the ordinary derived category,
the bounded inclusion, and the homotopy quotient comparison. -/
@[simp]
theorem hom (L : CochainComplex.Plus A) (n : ℤ) :
    (homologyIso F L n).hom =
      (DerivedCategory.homologyFunctorFactors B n).inv.app
          ((CochainComplex.Plus.ι B).obj (F.mapCochainComplexPlus.obj L)) ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Plus.Qh.compInclusionIso B).inv.app
            (F.mapCochainComplexPlus.obj L)) ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Qh.map
            ((Functor.Homotopy.Plus.quotientIso F).hom.app L)) := sorry

/-- The inverse comparison reverses the homotopy quotient, bounded inclusion, and ordinary
derived-category transports. -/
@[simp]
theorem inv (L : CochainComplex.Plus A) (n : ℤ) :
    (homologyIso F L n).inv =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Qh.map
            ((Functor.Homotopy.Plus.quotientIso F).inv.app L)) ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Plus.Qh.compInclusionIso B).hom.app
            (F.mapCochainComplexPlus.obj L)) ≫
        (DerivedCategory.homologyFunctorFactors B n).hom.app
          ((CochainComplex.Plus.ι B).obj (F.mapCochainComplexPlus.obj L)) := sorry

/-- The bounded-below homology comparisons are natural in the source complex. -/
@[reassoc]
theorem hom_naturality {L M : CochainComplex.Plus A} (f : L ⟶ M) (n : ℤ) :
    (F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
          HomologicalComplex.homologyFunctor B (up ℤ) n).map f ≫
        (homologyIso F M n).hom =
      (homologyIso F L n).hom ≫
        (HomotopyCategory.Plus.quotient A ⋙ F.toBoundedBelowDerived ⋙
          DerivedCategory.Plus.homologyFunctor B n).map f := sorry

/-- The inverse bounded-below homology comparisons are natural in the source complex. -/
@[reassoc]
theorem inv_naturality {L M : CochainComplex.Plus A} (f : L ⟶ M) (n : ℤ) :
    (HomotopyCategory.Plus.quotient A ⋙ F.toBoundedBelowDerived ⋙
          DerivedCategory.Plus.homologyFunctor B n).map f ≫
        (homologyIso F M n).inv =
      (homologyIso F L n).inv ≫
        (F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
          HomologicalComplex.homologyFunctor B (up ℤ) n).map f := sorry

end homologyIso

/-- The homology comparisons assemble into a natural isomorphism on bounded-below complexes. -/
@[stacks 015H "natural homology comparison for bounded-below termwise maps"]
noncomputable def homologyFunctorIso (n : ℤ) :
    F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n ≅
      HomotopyCategory.Plus.quotient A ⋙ F.toBoundedBelowDerived ⋙
        DerivedCategory.Plus.homologyFunctor B n :=
  Functor.HomologyComparison.pasteIso
    ⟨Functor.Homotopy.Plus.quotientIso F⟩
    ⟨HomotopyCategory.Plus.quotientCompιIso B⟩
    ⟨DerivedCategory.Plus.QhCompιIsoιCompQh B⟩
    (DerivedCategory.quotientCompQhIso B)
    (DerivedCategory.homologyFunctorFactors B n)

namespace homologyFunctorIso

/-- The component of the natural bounded-below homology comparison is `homologyIso`. -/
@[simp]
theorem app (L : CochainComplex.Plus A) (n : ℤ) :
    (homologyFunctorIso F n).app L = homologyIso F L n := sorry

end homologyFunctorIso

end CategoryTheory.Functor.Homotopy.Plus.Homology
