/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor.Naturality.Minus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Above

/-!
# Naturality of bounded-above homology comparisons

The comparison between ordinary homology of a termwise mapped bounded-above complex and
homology in the bounded-above derived category is natural in the additive functor. Named
source and target transformations hide the required whiskering from downstream users.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Minus.Homology

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- A natural transformation of additive functors acts on ordinary homology after termwise
mapping of bounded-above complexes. -/
@[stacks 015H "naturality source for bounded-above homology comparison"]
noncomputable abbrev cochainNatTrans (α : F ⟶ G) (n : ℤ) :
    Functor.Cochain.Minus.map F ⋙ CochainComplex.Minus.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n ⟶
      Functor.Cochain.Minus.map G ⋙ CochainComplex.Minus.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n :=
  Functor.whiskerRight (Functor.Cochain.Minus.natTrans α)
    (CochainComplex.Minus.ι B ⋙
      HomologicalComplex.homologyFunctor B (up ℤ) n)

/-- A natural transformation of additive functors acts after passage through the
bounded-above homotopy and derived categories and then taking homology. -/
@[stacks 015H "naturality target for bounded-above homology comparison"]
noncomputable abbrev derivedNatTrans (α : F ⟶ G) (n : ℤ) :
    HomotopyCategory.Minus.quotient A ⋙ F.toBoundedAboveDerived ⋙
        DerivedCategory.Minus.homologyFunctor B n ⟶
      HomotopyCategory.Minus.quotient A ⋙ G.toBoundedAboveDerived ⋙
        DerivedCategory.Minus.homologyFunctor B n :=
  Functor.whiskerLeft (HomotopyCategory.Minus.quotient A)
    (Functor.whiskerRight (NatTrans.toBoundedAboveDerived α)
      (DerivedCategory.Minus.homologyFunctor B n))

namespace homologyFunctorIso

/-- The forward bounded-above homology comparison is natural in the additive functor. -/
@[reassoc, stacks 015H "naturality of bounded-above termwise homology comparison"]
theorem naturality (α : F ⟶ G) (n : ℤ) :
    cochainNatTrans α n ≫ (homologyFunctorIso G n).hom =
      (homologyFunctorIso F n).hom ≫ derivedNatTrans α n := sorry

/-- Pointwise form of naturality for the forward bounded-above homology comparison. -/
@[reassoc]
theorem naturality_app (α : F ⟶ G) (L : CochainComplex.Minus A) (n : ℤ) :
    (cochainNatTrans α n).app L ≫ (homologyIso G L n).hom =
      (homologyIso F L n).hom ≫ (derivedNatTrans α n).app L := sorry

/-- The inverse bounded-above homology comparison is natural in the additive functor. -/
@[reassoc]
theorem inv_naturality (α : F ⟶ G) (n : ℤ) :
    derivedNatTrans α n ≫ (homologyFunctorIso G n).inv =
      (homologyFunctorIso F n).inv ≫ cochainNatTrans α n := sorry

/-- Pointwise form of naturality for the inverse bounded-above homology comparison. -/
@[reassoc]
theorem inv_naturality_app (α : F ⟶ G) (L : CochainComplex.Minus A) (n : ℤ) :
    (derivedNatTrans α n).app L ≫ (homologyIso G L n).inv =
      (homologyIso F L n).inv ≫ (cochainNatTrans α n).app L := sorry

end homologyFunctorIso

end CategoryTheory.Functor.Homotopy.Minus.Homology
