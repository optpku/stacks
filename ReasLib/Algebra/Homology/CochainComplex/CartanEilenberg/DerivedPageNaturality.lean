module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.ColumnFunctoriality
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.DerivedPages

/-!
# Naturality of derived-functor pages of Cartan--Eilenberg resolutions

The first page-one comparison with right derived functors is natural in the column direction.
Consequently, for each derived degree it assembles into an isomorphism of cochain complexes.
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

/-- The first page-one right-derived comparison intertwines a horizontal differential with the
corresponding map of right derived functors. -/
@[reassoc]
theorem rightDerivedIso_hom_map_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r : ℤ) (q : ℕ) :
    (rightDerivedIso I F p q).hom ≫ (F.rightDerived q).map (K.obj.d p r) =
      HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) (Int.ofNat q) ≫
        (rightDerivedIso I F r q).hom := sorry

/-- The inverse first page-one right-derived comparison is natural with respect to horizontal
differentials. -/
@[reassoc]
theorem rightDerivedIso_inv_naturality
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r : ℤ) (q : ℕ) :
    (F.rightDerived q).map (K.obj.d p r) ≫ (rightDerivedIso I F r q).inv =
      (rightDerivedIso I F p q).inv ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) (Int.ofNat q) := sorry

/-- The first page-one right-derived comparisons form a commuting square with every
horizontal differential. -/
theorem rightDerivedIso_commSq
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r : ℤ) (q : ℕ) :
    CommSq
      (f := (HomologicalComplex₂.First.PageOne.complex
        (I.mapBicomplex F) (Int.ofNat q)).d p r)
      (g := (rightDerivedIso I F p q).hom)
      (h := (rightDerivedIso I F r q).hom)
      (i := (F.rightDerived q).map (K.obj.d p r)) := sorry

/-- The componentwise right-derived comparison commutes with the differentials of the two
cochain complexes. -/
@[reassoc]
theorem rightDerivedIso_hom_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r : ℤ) (q : ℕ) :
    (rightDerivedIso I F p q).hom ≫
        (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj).d p r =
        (HomologicalComplex₂.First.PageOne.complex
        (I.mapBicomplex F) (Int.ofNat q)).d p r ≫
        (rightDerivedIso I F r q).hom := sorry

/-- Conjugating the first page differential by the right-derived comparison recovers the
source-facing page differential. -/
@[reassoc, stacks 015J "source differential computation for first page-one comparisons"]
theorem rightDerivedIso_source_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r : ℤ) (q : ℕ) :
    (rightDerivedIso I F p q).hom ≫
        (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj).d p r ≫
      (rightDerivedIso I F r q).inv =
    (HomologicalComplex₂.First.PageOne.complex
      (I.mapBicomplex F) (Int.ofNat q)).d p r := sorry

/-- Conjugating the source-facing first page differential by the inverse comparison recovers the
termwise right-derived differential. -/
@[reassoc, stacks 015J "target differential computation for first page-one comparisons"]
theorem rightDerivedIso_target_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r : ℤ) (q : ℕ) :
    (rightDerivedIso I F p q).inv ≫
        (HomologicalComplex₂.First.PageOne.complex
          (I.mapBicomplex F) (Int.ofNat q)).d p r ≫
      (rightDerivedIso I F r q).hom =
    (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj).d p r := sorry

/-- For a fixed derived degree, the first page-one complex is canonically the source complex
after applying the corresponding right derived functor termwise. -/
@[stacks 015J "the first page-one right-derived complex comparison"]
noncomputable def complexIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (q : ℕ) :
    HomologicalComplex₂.First.PageOne.complex (I.mapBicomplex F) (Int.ofNat q) ≅
      ((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => rightDerivedIso I F p q)
    (fun p r _ => rightDerivedIso_hom_d I F p r q)

/-- Evaluating `complexIso` in a horizontal degree recovers the objectwise
right-derived comparison. -/
@[simp]
theorem complexIso_app
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    HomologicalComplex.Hom.isoApp (complexIso I F q) p =
      rightDerivedIso I F p q := sorry

/-- The component of `complexIso` is the objectwise first page-one right-derived
comparison. -/
@[simp]
theorem complexIso_hom_f
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    (complexIso I F q).hom.f p = (rightDerivedIso I F p q).hom := sorry

/-- The inverse component of `complexIso` is the inverse objectwise first page-one
right-derived comparison. -/
@[simp]
theorem complexIso_inv_f
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    (complexIso I F q).inv.f p = (rightDerivedIso I F p q).inv := sorry

end First.PageOne

namespace First.PageTwo

/-- Taking horizontal homology of the first page-one right-derived complex comparison compares
the first page-two term
with the homology of the source complex after applying a right derived functor termwise. -/
@[stacks 015J "the first page-two right-derived homology comparison"]
noncomputable def rightDerivedHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    HomologicalComplex₂.First.PageTwo.entry (I.mapBicomplex F) p (Int.ofNat q) ≅
      (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj K.obj).homology p :=
  HomologicalComplex.homologyMapIso (First.PageOne.complexIso I F q) p

/-- The forward map of `rightDerivedHomologyIso` is the map on homology induced by the
forward whole-complex comparison. -/
@[simp]
theorem rightDerivedHomologyIso_hom
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    (rightDerivedHomologyIso I F p q).hom =
      HomologicalComplex.homologyMap (First.PageOne.complexIso I F q).hom p := sorry

/-- The inverse map of `rightDerivedHomologyIso` is the map on homology induced by the
inverse whole-complex comparison. -/
@[simp]
theorem rightDerivedHomologyIso_inv
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) :
    (rightDerivedHomologyIso I F p q).inv =
      HomologicalComplex.homologyMap (First.PageOne.complexIso I F q).inv p := sorry

end First.PageTwo

namespace Second.PageOne

/-- The chosen-resolution second page-one comparison commutes with every p-direction
differential. -/
@[stacks 015J "second page-one resolution naturality", reassoc]
theorem resolutionIso_hom_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p r q : ℤ) :
    (resolutionIso I F q).hom.f p ≫
        (Row.resolutionComplex I F q).d p r =
        (HomologicalComplex₂.Second.PageOne.complex
          (I.mapBicomplex F) q).d p r ≫
        (resolutionIso I F q).hom.f r := sorry

/-- Conjugating the second page-one differential by the chosen-resolution comparison recovers the
source-facing row differential. -/
@[stacks 015J "source differential computation for second page-one comparisons", reassoc]
theorem resolutionIso_source_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p r q : ℤ) :
    (resolutionIso I F q).hom.f p ≫
        (Row.resolutionComplex I F q).d p r ≫
      (resolutionIso I F q).inv.f r =
    (HomologicalComplex₂.Second.PageOne.complex
      (I.mapBicomplex F) q).d p r := sorry

/-- Conjugating the source-facing second page-one differential by the inverse comparison recovers
the chosen-resolution row differential. -/
@[stacks 015J "target differential computation for second page-one comparisons", reassoc]
theorem resolutionIso_target_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p r q : ℤ) :
    (resolutionIso I F q).inv.f p ≫
        (HomologicalComplex₂.Second.PageOne.complex
          (I.mapBicomplex F) q).d p r ≫
      (resolutionIso I F q).hom.f r =
    (Row.resolutionComplex I F q).d p r := sorry

/-- The inverse chosen-resolution second page-one comparison commutes with every p-direction
differential. -/
@[stacks 015J "inverse second page-one resolution naturality", reassoc]
theorem resolutionIso_inv_d
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p r q : ℤ) :
    (resolutionIso I F q).inv.f p ≫
        (HomologicalComplex₂.Second.PageOne.complex
          (I.mapBicomplex F) q).d p r =
      (Row.resolutionComplex I F q).d p r ≫
        (resolutionIso I F q).inv.f r := sorry

/-- The chosen-resolution second page-one comparisons form a commuting square with every
p-direction differential. -/
theorem resolutionIso_commSq
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p r q : ℤ) :
    CommSq
      (f := (HomologicalComplex₂.Second.PageOne.complex
        (I.mapBicomplex F) q).d p r)
      (g := (resolutionIso I F q).hom.f p)
      (h := (resolutionIso I F q).hom.f r)
      (i := (Row.resolutionComplex I F q).d p r) := sorry

end Second.PageOne

namespace Second.PageTwo

/-- The forward chosen-resolution page-two comparison is the homology map of the
chosen-resolution page-one comparison. -/
@[simp]
theorem resolutionHomologyIso_hom_homologyMap
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p : ℕ) (q : ℤ) :
    (resolutionHomologyIso I F (Int.ofNat p) q).hom =
      HomologicalComplex.homologyMap
        (Second.PageOne.resolutionIso I F q).hom (Int.ofNat p) := sorry

/-- The inverse chosen-resolution page-two comparison is the homology map of the inverse
chosen-resolution page-one comparison. -/
@[simp]
theorem resolutionHomologyIso_inv_homologyMap
    (I : CartanEilenbergResolution K) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] (p : ℕ) (q : ℤ) :
    (resolutionHomologyIso I F (Int.ofNat p) q).inv =
      HomologicalComplex.homologyMap
        (Second.PageOne.resolutionIso I F q).inv (Int.ofNat p) := sorry

end Second.PageTwo

end CochainComplex.CartanEilenbergResolution
