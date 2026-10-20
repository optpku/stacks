/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.DerivedPageNaturality
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Pages

/-!
# Naturality of derived Cartan--Eilenberg pages

The initial-page comparisons with right-derived functors are natural in maps of
Cartan--Eilenberg resolutions.  Consequently, maps with the same bundled source map induce the
same morphisms on the derived pages, so downstream constructions do not depend on a chosen lift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

namespace First.Derived

/-- The first page-one comparison with right-derived functors is natural in maps of
Cartan--Eilenberg resolutions. -/
@[stacks 015J "naturality of the first Cartan-Eilenberg derived page", reassoc]
theorem pageOneIso_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (First.pageOne f F (Int.ofNat q)).f p ≫
        (CartanEilenbergResolution.First.PageOne.rightDerivedIso J F p q).hom =
      (CartanEilenbergResolution.First.PageOne.rightDerivedIso I F p q).hom ≫
        (F.rightDerived q).map (f.base.hom.f p) := sorry

/-- Inverse naturality of the first Cartan-Eilenberg derived page-one comparison. -/
@[stacks 015J "inverse naturality of the first Cartan-Eilenberg derived page", reassoc]
theorem pageOneIso_inv_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (F.rightDerived q).map (f.base.hom.f p) ≫
        (CartanEilenbergResolution.First.PageOne.rightDerivedIso J F p q).inv =
      (CartanEilenbergResolution.First.PageOne.rightDerivedIso I F p q).inv ≫
        (First.pageOne f F (Int.ofNat q)).f p := sorry

/-- Conjugating the target map by the first Cartan-Eilenberg page-one comparison recovers the
pointwise page map. -/
@[stacks 015J "computation of the first Cartan-Eilenberg derived page", reassoc]
theorem pageOneIso_naturality_inv
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (CartanEilenbergResolution.First.PageOne.rightDerivedIso I F p q).hom ≫
        (F.rightDerived q).map (f.base.hom.f p) ≫
        (CartanEilenbergResolution.First.PageOne.rightDerivedIso J F p q).inv =
      (First.pageOne f F (Int.ofNat q)).f p := sorry

/-- Conjugating the pointwise first derived page-one map by the inverse comparison recovers the
right-derived map on the source component. -/
@[reassoc, stacks 015J "target-map computation of the pointwise first derived page-one comparison"]
theorem pageOneIso_target_map
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (CartanEilenbergResolution.First.PageOne.rightDerivedIso I F p q).inv ≫
        (First.pageOne f F (Int.ofNat q)).f p ≫
      (CartanEilenbergResolution.First.PageOne.rightDerivedIso J F p q).hom =
      (F.rightDerived q).map (f.base.hom.f p) := sorry

/-- Two lifts of the same source map induce the same first page-one map. -/
@[stacks 015J "independence of the first Cartan-Eilenberg derived page from a lift"]
theorem pageOne_eq_of_base_eq
    (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℕ)
    (hbase : f.base = g.base) :
    First.pageOne f F (Int.ofNat q) = First.pageOne g F (Int.ofNat q) := sorry

/-- The first page-two comparison with the homology of the termwise right-derived source
complex is natural in maps of Cartan--Eilenberg resolutions. -/
@[stacks 015J "naturality of the first Cartan-Eilenberg second page", reassoc]
theorem pageTwoIso_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    First.pageTwo f F p (Int.ofNat q) ≫
        (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso J F p q).hom =
      (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso I F p q).hom ≫
        HomologicalComplex.homologyMap
          (((F.rightDerived q).mapHomologicalComplex (up ℤ)).map f.base.hom) p := sorry

/-- Inverse naturality of the first Cartan-Eilenberg derived page-two comparison. -/
@[stacks 015J "inverse naturality of the first Cartan-Eilenberg derived page", reassoc]
theorem pageTwoIso_inv_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    HomologicalComplex.homologyMap
          (((F.rightDerived q).mapHomologicalComplex (up ℤ)).map f.base.hom) p ≫
        (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso J F p q).inv =
      (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso I F p q).inv ≫
        First.pageTwo f F p (Int.ofNat q) := sorry

/-- Conjugating the target map by the first Cartan-Eilenberg page-two comparison recovers the
pointwise page map. -/
@[stacks 015J "computation of the first Cartan-Eilenberg derived page", reassoc]
theorem pageTwoIso_naturality_inv
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso I F p q).hom ≫
        HomologicalComplex.homologyMap
          (((F.rightDerived q).mapHomologicalComplex (up ℤ)).map f.base.hom) p ≫
        (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso J F p q).inv =
      First.pageTwo f F p (Int.ofNat q) := sorry

/-- Conjugating the pointwise first derived page-two map by the inverse comparison recovers the
right-derived homology map. -/
@[reassoc, stacks 015J "target-map computation of the pointwise first derived page-two comparison"]
theorem pageTwoIso_target_map
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso I F p q).inv ≫
        First.pageTwo f F p (Int.ofNat q) ≫
      (CartanEilenbergResolution.First.PageTwo.rightDerivedHomologyIso J F p q).hom =
      HomologicalComplex.homologyMap
        (((F.rightDerived q).mapHomologicalComplex (up ℤ)).map f.base.hom) p := sorry

/-- Two lifts of the same source map induce the same first page-two map. -/
@[stacks 015J "independence of the first Cartan-Eilenberg second page from a lift"]
theorem pageTwo_eq_of_base_eq
    (f g : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    (hbase : f.base = g.base) :
    First.pageTwo f F p (Int.ofNat q) = First.pageTwo g F p (Int.ofNat q) := sorry

end First.Derived

namespace Second.Derived

/-- The second page-two comparison with right-derived functors of source homology is natural in
maps of Cartan--Eilenberg resolutions. -/
@[stacks 015J "naturality of the second Cartan-Eilenberg derived page", reassoc]
theorem pageTwoIso_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    Second.pageTwo f F (Int.ofNat p) q ≫
        (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso J F p q).hom =
      (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso I F p q).hom ≫
        (F.rightDerived p).map (HomologicalComplex.homologyMap f.base.hom q) := sorry

/-- Inverse naturality of the second Cartan-Eilenberg derived page-two comparison. -/
@[stacks 015J "inverse naturality of the second Cartan-Eilenberg derived page", reassoc]
theorem pageTwoIso_inv_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    (F.rightDerived p).map (HomologicalComplex.homologyMap f.base.hom q) ≫
        (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso J F p q).inv =
      (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso I F p q).inv ≫
        Second.pageTwo f F (Int.ofNat p) q := sorry

/-- Conjugating the target map by the second Cartan-Eilenberg page-two comparison recovers the
pointwise page map. -/
@[stacks 015J "computation of the second Cartan-Eilenberg derived page", reassoc]
theorem pageTwoIso_naturality_inv
    (f : Map I J) (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso I F p q).hom ≫
        (F.rightDerived p).map (HomologicalComplex.homologyMap f.base.hom q) ≫
        (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso J F p q).inv =
      Second.pageTwo f F (Int.ofNat p) q := sorry

/-- Conjugating the pointwise second derived page-two map by the inverse comparison recovers the
right-derived map on source homology. -/
@[reassoc, stacks 015J "target-map computation of the pointwise second derived page-two comparison"]
theorem pageTwoIso_target_map
    (f : Map I J) (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) :
    (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso I F p q).inv ≫
        Second.pageTwo f F (Int.ofNat p) q ≫
      (CartanEilenbergResolution.Second.PageTwo.rightDerivedIso J F p q).hom =
      (F.rightDerived p).map (HomologicalComplex.homologyMap f.base.hom q) := sorry

/-- Two lifts of the same source map induce the same second page-two map. -/
@[stacks 015J "independence of the second Cartan-Eilenberg derived page from a lift"]
theorem pageTwo_eq_of_base_eq
    (f g : Map I J) (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (p : ℕ) (q : ℤ) (hbase : f.base = g.base) :
    Second.pageTwo f F (Int.ofNat p) q = Second.pageTwo g F (Int.ofNat p) q := sorry

end Second.Derived

end CochainComplex.CartanEilenbergResolution.Map
