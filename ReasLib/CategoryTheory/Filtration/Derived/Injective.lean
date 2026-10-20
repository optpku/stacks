/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.FullSubcategory
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Target
public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered-Injective Models for Finite Filtered Derived Categories

The functor in this file has the actual bounded-below homotopy category of
finite filtered-injective objects as its source.  It is a composite through
the finite filtered homotopy category and its canonical bounded localization;
it does not choose a derived-category presentation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u vD uD

namespace CategoryTheory

namespace FilteredObject

namespace FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.FilteredInjective

/-- The canonical functor from bounded-below complexes of finite
filtered-injective objects to the bounded-below finite filtered derived
category. -/
@[stacks 015Q "filtered injective derived equivalence"]
noncomputable def functor :
    HomotopyCategory.Plus (Finite.FilteredInjective.category C) ⥤ Plus.Category C h_inverts :=
  (Finite.FilteredInjective.inclusion C).mapHomotopyCategoryPlus ⋙
    Plus.Quotient.functor C h_inverts

/-- The localizer morphism induced by including bounded-below finite
filtered-injective complexes into all bounded-below finite filtered complexes. -/
@[stacks 015Q "filtered injective derived equivalence"]
abbrev localizer :
    LocalizerMorphism
      ((Plus.QuasiIso C).inverseImage
        (Finite.FilteredInjective.inclusion C).mapHomotopyCategoryPlus)
      (Plus.QuasiIso C) :=
  LocalizerMorphism.ofEq rfl

section Resolutions

variable {C}

/-- The bounded-below homotopy object represented by the complex in a supplied strict
filtered-injective resolution. -/
noncomputable def resolutionObj
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    HomotopyCategory.Plus (Finite.FilteredInjective.category C) :=
  (HomotopyCategory.Plus.quotient (Finite.FilteredInjective.category C)).obj
    ((CochainComplex.Plus.TermsIn.toFullSubcategory
      (Finite.FilteredInjective.property C)).obj R.complex)

/-- The homotopy map carried by a map of supplied strict filtered-injective resolutions. -/
noncomputable def resolutionMap
    {K L : CochainComplex.Plus (Finite.category C)} {f : K ⟶ L}
    {R : CochainComplex.FilteredInjectivePlus.Resolution K}
    {S : CochainComplex.FilteredInjectivePlus.Resolution L}
    (m : CochainComplex.FilteredInjectivePlus.Resolution.Map f R S) :
    resolutionObj R ⟶ resolutionObj S :=
  (HomotopyCategory.Plus.quotient (Finite.FilteredInjective.category C)).map
    ((CochainComplex.Plus.TermsIn.toFullSubcategory
      (Finite.FilteredInjective.property C)).map m.complexMap)

/-- The homotopy comparison carried by a supplied strict filtered-injective resolution. -/
noncomputable def resolutionComparison
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    (HomotopyCategory.Plus.quotient (Finite.category C)).obj K ⟶
      (Finite.FilteredInjective.inclusion C).mapHomotopyCategoryPlus.obj
        (resolutionObj R) :=
  ObjectProperty.homMk
    ((HomotopyCategory.quotient (Finite.category C) (ComplexShape.up ℤ)).map R.ι)

/-- The homotopy comparison is natural in maps of supplied strict filtered-injective
resolutions. -/
@[reassoc]
theorem resolutionComparison_naturality
    {K L : CochainComplex.Plus (Finite.category C)} {f : K ⟶ L}
    {R : CochainComplex.FilteredInjectivePlus.Resolution K}
    {S : CochainComplex.FilteredInjectivePlus.Resolution L}
    (m : CochainComplex.FilteredInjectivePlus.Resolution.Map f R S) :
    resolutionComparison R ≫
        (Finite.FilteredInjective.inclusion C).mapHomotopyCategoryPlus.map
          (resolutionMap m) =
      (HomotopyCategory.Plus.quotient (Finite.category C)).map f ≫
        resolutionComparison S := by
  apply (HomotopyCategory.Plus.ι (Finite.category C)).map_injective
  change
    (HomotopyCategory.quotient (Finite.category C) (ComplexShape.up ℤ)).map R.ι ≫
        (HomotopyCategory.quotient (Finite.category C) (ComplexShape.up ℤ)).map m.hom =
      (HomotopyCategory.quotient (Finite.category C) (ComplexShape.up ℤ)).map f.hom ≫
        (HomotopyCategory.quotient (Finite.category C) (ComplexShape.up ℤ)).map S.ι
  rw [← Functor.map_comp, ← Functor.map_comp, m.ι_naturality]

/-- The homotopy comparison of a strict filtered-injective resolution is a filtered
quasi-isomorphism. -/
theorem resolutionComparison_quasiIso
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    Plus.QuasiIso C (resolutionComparison R) :=
  (Finite.Homotopy.quasiIso_quotient_map_iff C R.ι).2 R.isStrict.quasiIso

/-- Regard a supplied strict filtered-injective resolution as a right resolution for the
inclusion of bounded-below filtered-injective homotopy complexes. -/
noncomputable def rightResolution
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    (localizer C).RightResolution
      ((HomotopyCategory.Plus.quotient (Finite.category C)).obj K) where
  X₁ := resolutionObj R
  w := resolutionComparison R
  hw := resolutionComparison_quasiIso R

/-- A supplied strict filtered-injective resolution gives an isomorphism in the bounded-below
filtered derived category. The inverse is the formal inverse of its comparison in the canonical
localization. -/
noncomputable def resolutionIso
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    (Plus.Quotient.functor C h_inverts).obj
        ((HomotopyCategory.Plus.quotient (Finite.category C)).obj K) ≅
      (functor C h_inverts).obj (resolutionObj R) :=
  ObjectProperty.isoMk (Plus.property C h_inverts)
    (Localization.Construction.wIso
      ((HomotopyCategory.Plus.ι (Finite.category C)).map (resolutionComparison R))
      (resolutionComparison_quasiIso R))

/-- The forward resolution isomorphism is the localized comparison map. -/
@[simp]
theorem resolutionIso_hom
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    (resolutionIso h_inverts R).hom =
      (Plus.Quotient.functor C h_inverts).map (resolutionComparison R) := rfl

/-- Forgetting boundedness exposes the formal inverse used by the resolution isomorphism. -/
@[simp]
theorem resolutionIso_inv_hom
    {K : CochainComplex.Plus (Finite.category C)}
    (R : CochainComplex.FilteredInjectivePlus.Resolution K) :
    (resolutionIso h_inverts R).inv.hom =
      Localization.Construction.wInv
        ((HomotopyCategory.Plus.ι (Finite.category C)).map (resolutionComparison R))
        (resolutionComparison_quasiIso R) := rfl

end Resolutions

/-- The proposition that the filtered-injective model functor is an equivalence. -/
@[stacks 015Q "filtered injective derived equivalence"]
abbrev IsEquivalence : Prop := Functor.IsEquivalence (functor C h_inverts)

/-- Stacks 015Q: bounded-below complexes of finite filtered-injective objects
compute the bounded-below finite filtered derived category. -/
@[stacks 015Q]
instance isEquivalence [EnoughInjectives C] : IsEquivalence C h_inverts := sorry

/-- A named inverse-equivalence package for the filtered-injective model of the
bounded-below finite filtered derived category, constructed from an explicit equivalence
certificate. -/
@[stacks 015Q "filtered injective derived equivalence"]
noncomputable def equivalenceOf (h_equiv : IsEquivalence C h_inverts) :
    HomotopyCategory.Plus (Finite.FilteredInjective.category C) ≌ Plus.Category C h_inverts :=
  @Functor.asEquivalence _ _ _ _ _
    h_equiv

/-! The next entry is the canonical specialization used under enough injectives.  The
certificate-taking form above remains available for constructions whose equivalence proof is
transported from another source. -/

/-- The canonical filtered-injective equivalence under enough injectives.

This is the reusable data owner for the standard model; callers should use it instead of
reconstructing an `IsEquivalence` proof merely to feed `equivalenceOf`. -/
@[stacks 015Q "canonical filtered injective derived equivalence"]
noncomputable def equivalenceOfEnoughInjectives [EnoughInjectives C] :
    HomotopyCategory.Plus (Finite.FilteredInjective.category C) ≌ Plus.Category C h_inverts :=
  equivalenceOf C h_inverts (isEquivalence C h_inverts)

/-- The forward functor of the canonical filtered-injective equivalence. -/
@[simp, stacks 015Q "forward canonical filtered injective equivalence"]
theorem equivalenceOfEnoughInjectives_functor [EnoughInjectives C] :
    (equivalenceOfEnoughInjectives C h_inverts).functor = functor C h_inverts := sorry

/-- The inverse functor of the canonical filtered-injective equivalence is the inverse selected
by the canonical equivalence package. -/
@[stacks 015Q "inverse canonical filtered injective equivalence"]
theorem equivalenceOfEnoughInjectives_inverse [EnoughInjectives C] :
    (equivalenceOfEnoughInjectives C h_inverts).inverse =
      (equivalenceOf C h_inverts (isEquivalence C h_inverts)).inverse := sorry

section Comparison

variable {A : Type u} [_root_.CategoryTheory.Category.{v} A] [Abelian A]
variable [HasDerivedCategory (GradedObject ℤ A)]
variable {D : Type uD} [_root_.CategoryTheory.Category.{vD} D]
variable (hA : AssociatedGraded.Inverts A)

namespace RightDerived

/-- The canonical comparison between a bounded-below finite filtered
right-derived functor and its computation through the filtered-injective
model. -/
@[stacks 05U2 "filtered injective right-derived comparison"]
noncomputable def iso
    (h_equiv : IsEquivalence A hA)
    {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ D}
    {rightDerived : Plus.Category A hA ⥤ D}
    {onFilteredInjectives : HomotopyCategory.Plus (Finite.FilteredInjective.category A) ⥤ D}
    (α : source ⟶ Plus.Quotient.functor A hA ⋙ rightDerived)
    (β : source ⟶ Plus.Quotient.functor A hA ⋙
      (equivalenceOf A hA h_equiv).inverse ⋙ onFilteredInjectives)
    [Functor.IsRightDerivedFunctor rightDerived α (Plus.QuasiIso A)]
    [Functor.IsRightDerivedFunctor
      ((equivalenceOf A hA h_equiv).inverse ⋙ onFilteredInjectives)
      β (Plus.QuasiIso A)] :
    rightDerived ≅
      (equivalenceOf A hA h_equiv).inverse ⋙ onFilteredInjectives :=
  rightDerived.rightDerivedUnique
    ((equivalenceOf A hA h_equiv).inverse ⋙ onFilteredInjectives)
    α β (Plus.QuasiIso A)

/-- The canonical comparison with the filtered-injective model under enough injectives.

The source, candidate derived functor, and model functor are inferred from the two factorization
maps.  Thus standard callers supply only `α` and `β`. -/
@[stacks 05U2 "canonical filtered injective right-derived comparison"]
noncomputable def isoOfEnoughInjectives [EnoughInjectives A]
    {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ D}
    {rightDerived : Plus.Category A hA ⥤ D}
    {onFilteredInjectives : HomotopyCategory.Plus (Finite.FilteredInjective.category A) ⥤ D}
    (α : source ⟶ Plus.Quotient.functor A hA ⋙ rightDerived)
    (β : source ⟶ Plus.Quotient.functor A hA ⋙
      (equivalenceOfEnoughInjectives A hA).inverse ⋙ onFilteredInjectives)
    [Functor.IsRightDerivedFunctor rightDerived α (Plus.QuasiIso A)]
    [Functor.IsRightDerivedFunctor
      ((equivalenceOfEnoughInjectives A hA).inverse ⋙ onFilteredInjectives)
      β (Plus.QuasiIso A)] :
    rightDerived ≅
      (equivalenceOfEnoughInjectives A hA).inverse ⋙ onFilteredInjectives :=
  rightDerived.rightDerivedUnique
    ((equivalenceOfEnoughInjectives A hA).inverse ⋙ onFilteredInjectives)
    α β (Plus.QuasiIso A)

section Computation

variable (h_equiv : IsEquivalence A hA)
variable (source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ D)
variable (rightDerived : Plus.Category A hA ⥤ D)
variable (onFilteredInjectives : HomotopyCategory.Plus (Finite.FilteredInjective.category A) ⥤ D)
variable (α : source ⟶ Plus.Quotient.functor A hA ⋙ rightDerived)
variable (β : source ⟶ Plus.Quotient.functor A hA ⋙
  (equivalenceOf A hA h_equiv).inverse ⋙ onFilteredInjectives)
variable [Functor.IsRightDerivedFunctor rightDerived α (Plus.QuasiIso A)]
variable [Functor.IsRightDerivedFunctor
  ((equivalenceOf A hA h_equiv).inverse ⋙ onFilteredInjectives)
  β (Plus.QuasiIso A)]

/-- The filtered-injective comparison carries the given right-derived factorization to the
factorization through the filtered-injective model. -/
@[reassoc (attr := simp), stacks 05U2 "filtered injective right-derived factorization"]
theorem fac :
    α ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (iso hA h_equiv α β).hom = β := sorry

/-- Componentwise form of `RightDerived.fac`. -/
@[simp, stacks 05U2 "filtered injective right-derived factorization"]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    α.app X ≫
        (iso hA h_equiv α β).hom.app
          ((Plus.Quotient.functor A hA).obj X) = β.app X := sorry

/-- The inverse filtered-injective comparison carries the model factorization back to the given
right-derived factorization. -/
@[reassoc (attr := simp), stacks 05U2 "filtered injective inverse factorization"]
theorem inv_fac :
    β ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (iso hA h_equiv α β).inv = α := sorry

/-- Componentwise form of `RightDerived.inv_fac`. -/
@[simp, stacks 05U2 "filtered injective inverse factorization"]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    β.app X ≫
        (iso hA h_equiv α β).inv.app
          ((Plus.Quotient.functor A hA).obj X) = α.app X := sorry

end Computation

namespace isoOfEnoughInjectives

variable [EnoughInjectives A]
variable {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ D}
variable {rightDerived : Plus.Category A hA ⥤ D}
variable {onFilteredInjectives :
  HomotopyCategory.Plus (Finite.FilteredInjective.category A) ⥤ D}
variable (α : source ⟶ Plus.Quotient.functor A hA ⋙ rightDerived)
variable (β : source ⟶ Plus.Quotient.functor A hA ⋙
  (equivalenceOfEnoughInjectives A hA).inverse ⋙ onFilteredInjectives)
variable [Functor.IsRightDerivedFunctor rightDerived α (Plus.QuasiIso A)]
variable [Functor.IsRightDerivedFunctor
  ((equivalenceOfEnoughInjectives A hA).inverse ⋙ onFilteredInjectives)
  β (Plus.QuasiIso A)]

/-- The canonical filtered-injective comparison carries the original factorization to the
factorization through the standard filtered-injective model. -/
@[reassoc (attr := simp), stacks 05U2
  "canonical filtered injective right-derived factorization"]
theorem fac :
    α ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (isoOfEnoughInjectives hA α β).hom = β := sorry

/-- Component form of `isoOfEnoughInjectives.fac`. -/
@[simp, stacks 05U2 "canonical filtered injective right-derived factorization"]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    α.app X ≫
        (isoOfEnoughInjectives hA α β).hom.app
          ((Plus.Quotient.functor A hA).obj X) = β.app X := sorry

/-- The inverse canonical filtered-injective comparison carries the model factorization back to
the original one. -/
@[reassoc (attr := simp), stacks 05U2
  "canonical filtered injective inverse factorization"]
theorem inv_fac :
    β ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (isoOfEnoughInjectives hA α β).inv = α := sorry

/-- Component form of `isoOfEnoughInjectives.inv_fac`. -/
@[simp, stacks 05U2 "canonical filtered injective inverse factorization"]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    β.app X ≫
        (isoOfEnoughInjectives hA α β).inv.app
          ((Plus.Quotient.functor A hA).obj X) = α.app X := sorry

end isoOfEnoughInjectives
end RightDerived

end Comparison

end Plus.FilteredInjective

end FiniteDerived

end FilteredObject

end CategoryTheory
