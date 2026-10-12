/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Properties
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages.PreservesHomology

/-!
# Functorial row homology of Cartan--Eilenberg resolutions

The rows of a Cartan--Eilenberg resolution have injective cycles and boundaries.  Consequently,
every additive functor preserves their homology even when it does not preserve arbitrary
homology.  This file packages that comparison and identifies the second page-one complex with
the mapped injective resolution of the source homology object, including its sign rescaling.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K : CochainComplex.Plus A}

/-- The chosen homology resolution after applying an additive functor termwise. -/
abbrev Row.resolutionComplex
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    CochainComplex B ℤ :=
  (F.mapHomologicalComplex (up ℤ)).obj (I.homologyResolution q).cochainComplex

/-- Every additive functor preserves the homology of each row of a Cartan--Eilenberg
resolution. -/
instance Row.preservesLeftHomologyOf
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q p : ℤ) :
    F.PreservesLeftHomologyOf ((I.row q).sc p) := sorry

/-- Row homology after applying an additive functor is canonically the image of the original
row homology. -/
noncomputable def Row.mapHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q p : ℤ) :
    ((I.mapBicomplex F).flip.X q).homology p ≅ F.obj (Row.homology I q p) :=
  (I.row q).mapHomologyIso F p

/-- Row homology after applying an additive functor identifies with the corresponding term of
the mapped chosen homology resolution. -/
noncomputable def Row.resolutionMapIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q p : ℤ) :
    ((I.mapBicomplex F).flip.X q).homology p ≅
      (Row.resolutionComplex I F p).X q :=
  Row.mapHomologyIso I F q p ≪≫
    F.mapIso (Homology.resolutionToRow I q p).symm

namespace Second.PageOne

/-- The second page-one complex is canonically the functor applied to the horizontal-homology
column of the Cartan--Eilenberg double complex. -/
noncomputable def columnIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q : ℤ) :
    HomologicalComplex₂.Second.PageOne.complex (I.mapBicomplex F) q ≅
      (F.mapHomologicalComplex (up ℤ)).obj (I.homologyColumn q) :=
  HomologicalComplex₂.Map.Second.PageOne.iso I.bicomplex F q

/-- The page-one comparison to the homology column is the generic mapped row-homology
comparison. -/
@[simp]
theorem columnIso_hom_f
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q p : ℤ) :
    (columnIso I F q).hom.f p =
      (HomologicalComplex₂.Map.Second.PageOne.iso I.bicomplex F q).hom.f p := sorry

/-- The second page-one complex is canonically the mapped chosen homology resolution, with the
standard page-one sign removed. -/
@[stacks 015J "the second page-one complex comparison"]
noncomputable def resolutionIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q : ℤ) :
    HomologicalComplex₂.Second.PageOne.complex (I.mapBicomplex F) q ≅
      Row.resolutionComplex I F q :=
  columnIso I F q ≪≫ (Homology.mapResolutionIso I F q).symm

/-- The chosen-resolution comparison evaluates to the homology-column comparison followed by
the inverse mapped resolution comparison. -/
@[simp]
theorem resolutionIso_hom_f
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (q p : ℤ) :
    (resolutionIso I F q).hom.f p =
      (columnIso I F q).hom.f p ≫
        (Homology.mapResolutionIso I F q).inv.f p := sorry

end Second.PageOne

namespace Second.PageTwo

/-- The second page-two entry is canonically the homology of the mapped horizontal-homology
column. -/
noncomputable def columnIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p q : ℤ) :
    HomologicalComplex₂.Second.PageTwo.entry (I.mapBicomplex F) p q ≅
      ((F.mapHomologicalComplex (up ℤ)).obj (I.homologyColumn q)).homology p :=
  HomologicalComplex₂.Map.Second.PageTwo.iso I.bicomplex F p q

/-- The second page-two entry is canonically the homology of the mapped chosen resolution of
the source homology object. -/
noncomputable def resolutionHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p q : ℤ) :
    HomologicalComplex₂.Second.PageTwo.entry (I.mapBicomplex F) p q ≅
      (Row.resolutionComplex I F q).homology p :=
  columnIso I F p q ≪≫ (Homology.mapResolutionHomologyIso I F q p).symm

/-- The chosen-resolution second-page comparison factors through the mapped homology column. -/
@[simp]
theorem resolutionHomologyIso_hom
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p q : ℤ) :
    (resolutionHomologyIso I F p q).hom =
      (columnIso I F p q).hom ≫
        (Homology.mapResolutionHomologyIso I F q p).inv := sorry

end Second.PageTwo

end CochainComplex.CartanEilenbergResolution
