/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor.Naturality.Plus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Below

/-!
# Naturality of bounded-below homology comparisons

The comparison between ordinary homology of a termwise mapped bounded-below complex and
homology in the bounded-below derived category is natural in the additive functor. Named
source and target transformations hide the required whiskering from downstream users.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Plus.Homology

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- A natural transformation of additive functors acts on ordinary homology after termwise
mapping of bounded-below complexes. -/
@[stacks 015H "naturality source for bounded-below homology comparison"]
noncomputable abbrev cochainNatTrans (α : F ⟶ G) (n : ℤ) :
    F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n ⟶
      G.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
        HomologicalComplex.homologyFunctor B (up ℤ) n :=
  Functor.whiskerRight (Functor.Cochain.Plus.natTrans α)
    (CochainComplex.Plus.ι B ⋙
      HomologicalComplex.homologyFunctor B (up ℤ) n)

/-- A natural transformation of additive functors acts after passage through the
bounded-below homotopy and derived categories and then taking homology. -/
@[stacks 015H "naturality target for bounded-below homology comparison"]
noncomputable abbrev derivedNatTrans (α : F ⟶ G) (n : ℤ) :
    HomotopyCategory.Plus.quotient A ⋙ F.toBoundedBelowDerived ⋙
        DerivedCategory.Plus.homologyFunctor B n ⟶
      HomotopyCategory.Plus.quotient A ⋙ G.toBoundedBelowDerived ⋙
        DerivedCategory.Plus.homologyFunctor B n :=
  Functor.whiskerLeft (HomotopyCategory.Plus.quotient A)
    (Functor.whiskerRight (NatTrans.toBoundedBelowDerived α)
      (DerivedCategory.Plus.homologyFunctor B n))

namespace homologyFunctorIso

/-- The forward bounded-below homology comparison is natural in the additive functor. -/
@[reassoc, stacks 015H "naturality of bounded-below termwise homology comparison"]
theorem naturality (α : F ⟶ G) (n : ℤ) :
    cochainNatTrans α n ≫ (homologyFunctorIso G n).hom =
      (homologyFunctorIso F n).hom ≫ derivedNatTrans α n := sorry

/-- Pointwise form of naturality for the forward bounded-below homology comparison. -/
@[reassoc]
theorem naturality_app (α : F ⟶ G) (L : CochainComplex.Plus A) (n : ℤ) :
    (cochainNatTrans α n).app L ≫ (homologyIso G L n).hom =
      (homologyIso F L n).hom ≫ (derivedNatTrans α n).app L := sorry

/-- The inverse bounded-below homology comparison is natural in the additive functor. -/
@[reassoc]
theorem inv_naturality (α : F ⟶ G) (n : ℤ) :
    derivedNatTrans α n ≫ (homologyFunctorIso G n).inv =
      (homologyFunctorIso F n).inv ≫ cochainNatTrans α n := sorry

/-- Pointwise form of naturality for the inverse bounded-below homology comparison. -/
@[reassoc]
theorem inv_naturality_app (α : F ⟶ G) (L : CochainComplex.Plus A) (n : ℤ) :
    (derivedNatTrans α n).app L ≫ (homologyIso G L n).inv =
      (homologyIso F L n).inv ≫ (cochainNatTrans α n).app L := sorry

end homologyFunctorIso

end CategoryTheory.Functor.Homotopy.Plus.Homology
