/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Pages

/-!
# Initial-page functors on Cartan--Eilenberg resolutions

The first two pages associated with either standard filtration are assembled into functors on
bundled Cartan--Eilenberg resolutions.  This is the functorial owner behind the pointwise maps in
`CartanEilenbergResolution.Map.First` and `CartanEilenbergResolution.Map.Second`.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [CategoryWithHomology B]

namespace First

/-- The first page-one complexes, functorial in bundled Cartan--Eilenberg resolutions. -/
@[stacks 015J "first Cartan-Eilenberg page-one functor"]
noncomputable def pageOne (F : A ⥤ B) [F.Additive] (q : ℤ) :
    Bundled A ⥤ CochainComplex B ℤ where
  obj X := HomologicalComplex₂.First.PageOne.complex (X.resolution.mapBicomplex F) q
  map f := Map.First.pageOne f F q
  map_id X := Map.First.pageOne_id X.resolution F q
  map_comp f g := Map.First.pageOne_comp f g F q

/-- A fixed entry of the first page-two construction, functorial in bundled
Cartan--Eilenberg resolutions. -/
@[stacks 015J "first Cartan-Eilenberg page-two functor"]
noncomputable def pageTwo (F : A ⥤ B) [F.Additive] (p q : ℤ) : Bundled A ⥤ B where
  obj X := HomologicalComplex₂.First.PageTwo.entry (X.resolution.mapBicomplex F) p q
  map f := Map.First.pageTwo f F p q
  map_id X := Map.First.pageTwo_id X.resolution F p q
  map_comp f g := Map.First.pageTwo_comp f g F p q

/-- Object computation for the first page-one functor. -/
@[simp, stacks 015J "first Cartan-Eilenberg page-one functor"]
theorem pageOne_obj (F : A ⥤ B) [F.Additive] (q : ℤ) (X : Bundled A) :
    (pageOne F q).obj X =
      HomologicalComplex₂.First.PageOne.complex (X.resolution.mapBicomplex F) q := sorry

/-- Morphism computation for the first page-one functor. -/
@[simp, stacks 015J "first Cartan-Eilenberg page-one functor"]
theorem pageOne_map (F : A ⥤ B) [F.Additive] (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageOne F q).map f = Map.First.pageOne f F q := sorry

/-- Object computation for the first page-two functor. -/
@[simp, stacks 015J "first Cartan-Eilenberg page-two functor"]
theorem pageTwo_obj (F : A ⥤ B) [F.Additive] (p q : ℤ) (X : Bundled A) :
    (pageTwo F p q).obj X =
      HomologicalComplex₂.First.PageTwo.entry (X.resolution.mapBicomplex F) p q := sorry

/-- Morphism computation for the first page-two functor. -/
@[simp, stacks 015J "first Cartan-Eilenberg page-two functor"]
theorem pageTwo_map (F : A ⥤ B) [F.Additive] (p q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageTwo F p q).map f = Map.First.pageTwo f F p q := sorry

end First

namespace Second

/-- The second page-one complexes, functorial in bundled Cartan--Eilenberg resolutions. -/
@[stacks 015J "second Cartan-Eilenberg page-one functor"]
noncomputable def pageOne (F : A ⥤ B) [F.Additive] (q : ℤ) :
    Bundled A ⥤ CochainComplex B ℤ where
  obj X := HomologicalComplex₂.Second.PageOne.complex (X.resolution.mapBicomplex F) q
  map f := Map.Second.pageOne f F q
  map_id X := Map.Second.pageOne_id X.resolution F q
  map_comp f g := Map.Second.pageOne_comp f g F q

/-- A fixed entry of the second page-two construction, functorial in bundled
Cartan--Eilenberg resolutions. -/
@[stacks 015J "second Cartan-Eilenberg page-two functor"]
noncomputable def pageTwo (F : A ⥤ B) [F.Additive] (p q : ℤ) : Bundled A ⥤ B where
  obj X := HomologicalComplex₂.Second.PageTwo.entry (X.resolution.mapBicomplex F) p q
  map f := Map.Second.pageTwo f F p q
  map_id X := Map.Second.pageTwo_id X.resolution F p q
  map_comp f g := Map.Second.pageTwo_comp f g F p q

/-- Object computation for the second page-one functor. -/
@[simp, stacks 015J "second Cartan-Eilenberg page-one functor"]
theorem pageOne_obj (F : A ⥤ B) [F.Additive] (q : ℤ) (X : Bundled A) :
    (pageOne F q).obj X =
      HomologicalComplex₂.Second.PageOne.complex (X.resolution.mapBicomplex F) q := sorry

/-- Morphism computation for the second page-one functor. -/
@[simp, stacks 015J "second Cartan-Eilenberg page-one functor"]
theorem pageOne_map (F : A ⥤ B) [F.Additive] (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageOne F q).map f = Map.Second.pageOne f F q := sorry

/-- Object computation for the second page-two functor. -/
@[simp, stacks 015J "second Cartan-Eilenberg page-two functor"]
theorem pageTwo_obj (F : A ⥤ B) [F.Additive] (p q : ℤ) (X : Bundled A) :
    (pageTwo F p q).obj X =
      HomologicalComplex₂.Second.PageTwo.entry (X.resolution.mapBicomplex F) p q := sorry

/-- Morphism computation for the second page-two functor. -/
@[simp, stacks 015J "second Cartan-Eilenberg page-two functor"]
theorem pageTwo_map (F : A ⥤ B) [F.Additive] (p q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (pageTwo F p q).map f = Map.Second.pageTwo f F p q := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Bundled
