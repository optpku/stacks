module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization.Computation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Pasting

/-!
# Homology of termwise maps on bounded complexes

For an additive functor, ordinary homology after mapping a bounded complex agrees naturally
with homology after passing through the bounded homotopy and derived categories. This does not
require a derived functor of the additive functor.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Bounded.Homology

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]

/-- Ordinary homology of a termwise mapped bounded complex agrees with homology after
passing through the bounded derived category. -/
@[stacks 015H "homology after mapping a bounded complex"]
noncomputable def homologyIso (L : CochainComplex.Bounded A) (n : ℤ) :
    ((CochainComplex.Bounded.ι B).obj ((Functor.Cochain.Bounded.map F).obj L)).homology n ≅
      (DerivedCategory.Bounded.homologyFunctor B n).obj
        (F.toBoundedDerived.obj ((HomotopyCategory.Bounded.quotient A).obj L)) :=
  (DerivedCategory.homologyFunctorFactors B n).symm.app
      ((CochainComplex.Bounded.ι B).obj ((Functor.Cochain.Bounded.map F).obj L)) ≪≫
    (DerivedCategory.homologyFunctor B n).mapIso
      ((DerivedCategory.Bounded.Qh.compInclusionIso B).symm.app
        ((HomotopyCategory.Bounded.quotient B).obj
          ((Functor.Cochain.Bounded.map F).obj L))) ≪≫
    (DerivedCategory.Bounded.homologyFunctor B n).mapIso
      ((DerivedCategory.Bounded.Qh B).mapIso
        ((Functor.Homotopy.Bounded.quotientIso F).app L))

namespace homologyIso

/-- The forward comparison is the canonical transport through the ordinary derived category,
the bounded inclusion, and the homotopy quotient comparison. -/
@[simp]
theorem hom (L : CochainComplex.Bounded A) (n : ℤ) :
    (homologyIso F L n).hom =
      (DerivedCategory.homologyFunctorFactors B n).inv.app
          ((CochainComplex.Bounded.ι B).obj ((Functor.Cochain.Bounded.map F).obj L)) ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Bounded.Qh.compInclusionIso B).inv.app
            ((HomotopyCategory.Bounded.quotient B).obj
              ((Functor.Cochain.Bounded.map F).obj L))) ≫
        (DerivedCategory.Bounded.homologyFunctor B n).map
          ((DerivedCategory.Bounded.Qh B).map
            ((Functor.Homotopy.Bounded.quotientIso F).hom.app L)) := sorry

/-- The inverse comparison reverses the homotopy quotient, bounded inclusion, and ordinary
derived-category transports. -/
@[simp]
theorem inv (L : CochainComplex.Bounded A) (n : ℤ) :
    (homologyIso F L n).inv =
      (DerivedCategory.Bounded.homologyFunctor B n).map
          ((DerivedCategory.Bounded.Qh B).map
            ((Functor.Homotopy.Bounded.quotientIso F).inv.app L)) ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Bounded.Qh.compInclusionIso B).hom.app
            ((HomotopyCategory.Bounded.quotient B).obj
              ((Functor.Cochain.Bounded.map F).obj L))) ≫
        (DerivedCategory.homologyFunctorFactors B n).hom.app
          ((CochainComplex.Bounded.ι B).obj
            ((Functor.Cochain.Bounded.map F).obj L)) := sorry

/-- The bounded homology comparisons are natural in the source complex. -/
@[reassoc]
theorem hom_naturality {L M : CochainComplex.Bounded A} (f : L ⟶ M) (n : ℤ) :
    (Functor.Cochain.Bounded.map F ⋙ CochainComplex.Bounded.ι B ⋙
          HomologicalComplex.homologyFunctor B (up ℤ) n).map f ≫
        (homologyIso F M n).hom =
      (homologyIso F L n).hom ≫
        (HomotopyCategory.Bounded.quotient A ⋙ F.toBoundedDerived ⋙
          DerivedCategory.Bounded.homologyFunctor B n).map f := sorry

/-- The inverse bounded homology comparisons are natural in the source complex. -/
@[reassoc]
theorem inv_naturality {L M : CochainComplex.Bounded A} (f : L ⟶ M) (n : ℤ) :
    (HomotopyCategory.Bounded.quotient A ⋙ F.toBoundedDerived ⋙
          DerivedCategory.Bounded.homologyFunctor B n).map f ≫
        (homologyIso F M n).inv =
      (homologyIso F L n).inv ≫
        (Functor.Cochain.Bounded.map F ⋙ CochainComplex.Bounded.ι B ⋙
          HomologicalComplex.homologyFunctor B (up ℤ) n).map f := sorry

end homologyIso

/-- The homology comparisons assemble into a natural isomorphism on bounded complexes. -/
@[stacks 015H "natural homology comparison for bounded termwise maps"]
noncomputable def homologyFunctorIso (n : ℤ) :
    Functor.Cochain.Bounded.map F ⋙ CochainComplex.Bounded.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n ≅
      HomotopyCategory.Bounded.quotient A ⋙ F.toBoundedDerived ⋙
        DerivedCategory.Bounded.homologyFunctor B n :=
  Functor.HomologyComparison.pasteIso
    ⟨Functor.Homotopy.Bounded.quotientIso F⟩
    ⟨HomotopyCategory.Bounded.quotientCompιIso B⟩
    ⟨DerivedCategory.Bounded.Qh.compInclusionIso B⟩
    (DerivedCategory.quotientCompQhIso B)
    (DerivedCategory.homologyFunctorFactors B n)

namespace homologyFunctorIso

/-- The component of the natural bounded homology comparison is `homologyIso`. -/
@[simp]
theorem app (L : CochainComplex.Bounded A) (n : ℤ) :
    (homologyFunctorIso F n).app L = homologyIso F L n := sorry

end homologyFunctorIso

end CategoryTheory.Functor.Homotopy.Bounded.Homology
