/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.RowFunctoriality
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived

/-!
# Derived-functor pages of a Cartan--Eilenberg resolution

This file gives the two derived-functor identifications used most often downstream.  The first
page of the column filtration computes the right derived functors of the terms of the source
complex.  After taking row homology first, the second page computes the right derived functors
of the source homology objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K : CochainComplex.Plus A}

namespace First.PageOne

/-- The first page-one entry in nonnegative vertical degree computes the corresponding right
derived functor on the source term. -/
@[stacks 015J "the first page-one derived-functor identification"]
noncomputable def rightDerivedIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] (p : ℤ) (q : ℕ) :
    HomologicalComplex₂.First.PageOne.entry (I.mapBicomplex F) p (Int.ofNat q) ≅
      (F.rightDerived q).obj (K.obj.X p) :=
  (Column.mapResolutionHomologyIso I F p (Int.ofNat q)).symm ≪≫
    InjectiveResolution.RightDerived.homologyIso (I.columnResolution p) F q

/-- The forward first page-one right-derived comparison is the inverse chosen-column homology
comparison followed by the injective-resolution computation of the right derived functor. -/
@[simp]
theorem rightDerivedIso_hom
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    (rightDerivedIso I F p q).hom =
      (Column.mapResolutionHomologyIso I F p (Int.ofNat q)).inv ≫
        (InjectiveResolution.RightDerived.homologyIso (I.columnResolution p) F q).hom := sorry

/-- The inverse first page-one right-derived comparison is the inverse injective-resolution
computation followed by the chosen-column homology comparison. -/
@[simp]
theorem rightDerivedIso_inv
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    (rightDerivedIso I F p q).inv =
      (InjectiveResolution.RightDerived.homologyIso (I.columnResolution p) F q).inv ≫
        (Column.mapResolutionHomologyIso I F p (Int.ofNat q)).hom := sorry

end First.PageOne

namespace Second.PageTwo

/-- The second page-two entry in nonnegative horizontal degree computes the corresponding right
derived functor on the source homology object. -/
@[stacks 015J "the second page-two derived-functor identification"]
noncomputable def rightDerivedIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    HomologicalComplex₂.Second.PageTwo.entry (I.mapBicomplex F) (Int.ofNat p) q ≅
      (F.rightDerived p).obj (K.obj.homology q) :=
  Second.PageTwo.resolutionHomologyIso I F (Int.ofNat p) q ≪≫
    InjectiveResolution.RightDerived.homologyIso (I.homologyResolution q) F p

/-- The forward second page-two right-derived comparison is the chosen homology-resolution
comparison followed by the injective-resolution computation. -/
@[simp]
theorem rightDerivedIso_hom
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    (rightDerivedIso I F p q).hom =
      (Second.PageTwo.resolutionHomologyIso I F (Int.ofNat p) q).hom ≫
        (InjectiveResolution.RightDerived.homologyIso (I.homologyResolution q) F p).hom := sorry

/-- The inverse second page-two right-derived comparison first uses the inverse
injective-resolution computation and then the inverse chosen homology-resolution comparison. -/
@[simp]
theorem rightDerivedIso_inv
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    (rightDerivedIso I F p q).inv =
      (InjectiveResolution.RightDerived.homologyIso (I.homologyResolution q) F p).inv ≫
        (Second.PageTwo.resolutionHomologyIso I F (Int.ofNat p) q).inv := sorry

end Second.PageTwo

end CochainComplex.CartanEilenbergResolution
