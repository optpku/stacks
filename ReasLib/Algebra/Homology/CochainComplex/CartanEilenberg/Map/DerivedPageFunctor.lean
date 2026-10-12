/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.DerivedPages
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.DerivedFunctor

/-!
# Derived-page functors for Cartan--Eilenberg resolutions

The pointwise comparisons between the initial pages of a Cartan--Eilenberg resolution and
right-derived functors are assembled into natural isomorphisms on bundled resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace First.Derived

/-- Naturality of the first page-one whole-complex comparison on bundled resolutions. -/
@[reassoc, stacks 015J "naturality of the first derived page-one comparison"]
theorem pageOneIso_naturality (F : A ⥤ B) [F.Additive] (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (First.pageOne F (Int.ofNat q)).map f ≫
        (CartanEilenbergResolution.First.PageOne.complexIso
          Y.resolution F q).hom =
      (CartanEilenbergResolution.First.PageOne.complexIso
        X.resolution F q).hom ≫ (complex F q).map f := sorry

/-- The first page-one complex is naturally the termwise right-derived source complex. -/
@[stacks 015J "first derived page-one natural comparison"]
noncomputable def pageOneIso (F : A ⥤ B) [F.Additive] (q : ℕ) :
    First.pageOne F (Int.ofNat q) ≅ complex F q :=
  NatIso.ofComponents
    (fun X => CartanEilenbergResolution.First.PageOne.complexIso
      X.resolution F q)
    (pageOneIso_naturality F q)

/-- The forward component of the first derived page-one comparison is the pointwise
whole-complex comparison. -/
@[simp, stacks 015J "first derived page-one natural comparison"]
theorem pageOneIso_hom_app (F : A ⥤ B) [F.Additive]
    (q : ℕ) (X : Bundled A) :
    (pageOneIso F q).hom.app X =
      (CartanEilenbergResolution.First.PageOne.complexIso
        X.resolution F q).hom := sorry

/-- The inverse component of the first derived page-one comparison is the inverse pointwise
whole-complex comparison. -/
@[simp, stacks 015J "first derived page-one natural comparison"]
theorem pageOneIso_inv_app (F : A ⥤ B) [F.Additive]
    (q : ℕ) (X : Bundled A) :
    (pageOneIso F q).inv.app X =
      (CartanEilenbergResolution.First.PageOne.complexIso
        X.resolution F q).inv := sorry

/-- Inverse naturality of the first derived page-one comparison. -/
@[reassoc, stacks 015J "inverse naturality of the first derived page-one comparison"]
theorem pageOneIso_inv_naturality (F : A ⥤ B) [F.Additive] (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (complex F q).map f ≫ (pageOneIso F q).inv.app Y =
      (pageOneIso F q).inv.app X ≫ (First.pageOne F (Int.ofNat q)).map f := sorry

/-- Conjugating the target map by the first derived page-one comparison recovers the source map.
-/
@[reassoc, stacks 015J "computation of the first derived page-one map"]
theorem pageOneIso_naturality_inv (F : A ⥤ B) [F.Additive] (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageOneIso F q).hom.app X ≫ (complex F q).map f ≫
        (pageOneIso F q).inv.app Y =
      (First.pageOne F (Int.ofNat q)).map f := sorry

/-- Conjugating the first derived page-one map by the inverse comparison recovers the
termwise right-derived map. -/
@[reassoc, stacks 015J "target-map computation of the first derived page-one comparison"]
theorem pageOneIso_target_map (F : A ⥤ B) [F.Additive] (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageOneIso F q).inv.app X ≫
        (First.pageOne F (Int.ofNat q)).map f ≫
      (pageOneIso F q).hom.app Y =
      (complex F q).map f := sorry

/-- Naturality of the first page-two right-derived homology comparison. -/
@[reassoc, stacks 015J "naturality of the first derived page-two comparison"]
theorem pageTwoIso_naturality (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (First.pageTwo F p (Int.ofNat q)).map f ≫
        (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso
          Y.resolution F p q).hom =
      (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso
        X.resolution F p q).hom ≫ (homology F p q).map f := sorry

/-- The first page-two entry is naturally the cohomology of the termwise right-derived
source complex. -/
@[stacks 015J "first derived page-two natural comparison"]
noncomputable def pageTwoIso (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    First.pageTwo F p (Int.ofNat q) ≅ homology F p q :=
  NatIso.ofComponents
    (fun X => CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso
      X.resolution F p q)
    (pageTwoIso_naturality F p q)

/-- The forward component of the first derived page-two comparison is the pointwise
right-derived homology comparison. -/
@[simp, stacks 015J "first derived page-two natural comparison"]
theorem pageTwoIso_hom_app (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) (X : Bundled A) :
    (pageTwoIso F p q).hom.app X =
      (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso
        X.resolution F p q).hom := sorry

/-- The inverse component of the first derived page-two comparison is the inverse pointwise
right-derived homology comparison. -/
@[simp, stacks 015J "first derived page-two natural comparison"]
theorem pageTwoIso_inv_app (F : A ⥤ B) [F.Additive]
    (p : ℤ) (q : ℕ) (X : Bundled A) :
    (pageTwoIso F p q).inv.app X =
      (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso
        X.resolution F p q).inv := sorry

/-- Inverse naturality of the first derived page-two comparison. -/
@[reassoc, stacks 015J "inverse naturality of the first derived page-two comparison"]
theorem pageTwoIso_inv_naturality (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (homology F p q).map f ≫ (pageTwoIso F p q).inv.app Y =
      (pageTwoIso F p q).inv.app X ≫
        (First.pageTwo F p (Int.ofNat q)).map f := sorry

/-- Conjugating the target map by the first derived page-two comparison recovers the source map.
-/
@[reassoc, stacks 015J "computation of the first derived page-two map"]
theorem pageTwoIso_naturality_inv (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageTwoIso F p q).hom.app X ≫ (homology F p q).map f ≫
        (pageTwoIso F p q).inv.app Y =
      (First.pageTwo F p (Int.ofNat q)).map f := sorry

/-- Conjugating the first derived page-two map by the inverse comparison recovers the
termwise right-derived homology map. -/
@[reassoc, stacks 015J "target-map computation of the first derived page-two comparison"]
theorem pageTwoIso_target_map (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageTwoIso F p q).inv.app X ≫
        (First.pageTwo F p (Int.ofNat q)).map f ≫
      (pageTwoIso F p q).hom.app Y =
      (homology F p q).map f := sorry

end First.Derived

namespace Second.Derived

/-- Naturality of the second page-two right-derived comparison. -/
@[reassoc, stacks 015J "naturality of the second derived page-two comparison"]
theorem pageTwoIso_naturality (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (Second.pageTwo F (Int.ofNat p) q).map f ≫
        (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso
          Y.resolution F p q).hom =
      (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso
        X.resolution F p q).hom ≫ (homology F p q).map f := sorry

/-- The second page-two entry is naturally the right-derived functor of source cohomology. -/
@[stacks 015J "second derived page-two natural comparison"]
noncomputable def pageTwoIso (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ) :
    Second.pageTwo F (Int.ofNat p) q ≅ homology F p q :=
  NatIso.ofComponents
    (fun X => CartanEilenbergResolution.Second.PageTwo.rightDerivedIso
      X.resolution F p q)
    (pageTwoIso_naturality F p q)

/-- The forward component of the second derived page-two comparison is the pointwise
right-derived comparison. -/
@[simp, stacks 015J "second derived page-two natural comparison"]
theorem pageTwoIso_hom_app (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ) (X : Bundled A) :
    (pageTwoIso F p q).hom.app X =
      (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso
        X.resolution F p q).hom := sorry

/-- The inverse component of the second derived page-two comparison is the inverse pointwise
right-derived comparison. -/
@[simp, stacks 015J "second derived page-two natural comparison"]
theorem pageTwoIso_inv_app (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ) (X : Bundled A) :
    (pageTwoIso F p q).inv.app X =
      (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso
        X.resolution F p q).inv := sorry

/-- Inverse naturality of the second derived page-two comparison. -/
@[reassoc, stacks 015J "inverse naturality of the second derived page-two comparison"]
theorem pageTwoIso_inv_naturality (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (homology F p q).map f ≫ (pageTwoIso F p q).inv.app Y =
      (pageTwoIso F p q).inv.app X ≫
        (Second.pageTwo F (Int.ofNat p) q).map f := sorry

/-- Conjugating the target map by the second derived page-two comparison recovers the source map.
-/
@[reassoc, stacks 015J "computation of the second derived page-two map"]
theorem pageTwoIso_naturality_inv (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageTwoIso F p q).hom.app X ≫ (homology F p q).map f ≫
        (pageTwoIso F p q).inv.app Y =
      (Second.pageTwo F (Int.ofNat p) q).map f := sorry

/-- Conjugating the second derived page-two map by the inverse comparison recovers the
right-derived map on source homology. -/
@[reassoc, stacks 015J "target-map computation of the second derived page-two comparison"]
theorem pageTwoIso_target_map (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (p : ℕ) (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageTwoIso F p q).inv.app X ≫
        (Second.pageTwo F (Int.ofNat p) q).map f ≫
      (pageTwoIso F p q).hom.app Y =
      (homology F p q).map f := sorry

end Second.Derived

end CochainComplex.CartanEilenbergResolution.Bundled
