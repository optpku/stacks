/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale.Functor
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages

/-!
# Initial-page maps of Cartan--Eilenberg resolutions

A map of mapped Cartan--Eilenberg double complexes induces maps on both page-one complexes and
their page-two homology objects.  Derived-functor comparisons are kept in the separate
`CartanEilenberg.Map.DerivedPages` leaf.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [CategoryWithHomology B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

namespace First

/-- The induced map on the first page-one complex in vertical homology degree `q`. -/
@[stacks 015J "first Cartan-Eilenberg page-one map"]
noncomputable abbrev pageOne
    (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    HomologicalComplex₂.First.PageOne.complex (I.mapBicomplex F) q ⟶
      HomologicalComplex₂.First.PageOne.complex (J.mapBicomplex F) q :=
  ((HomologicalComplex.homologyFunctor B (up ℤ) q).mapHomologicalComplex (up ℤ)).map
    (mapped f F)

/-- The first page-one map in horizontal degree `p` is the homology map of the corresponding
mapped column map. -/
@[simp]
theorem pageOne_f
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    (pageOne f F q).f p =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (up ℤ)).map (column f p)) q := sorry

/-- The induced map on a first page-two entry. -/
@[stacks 015J "first Cartan-Eilenberg page-two map"]
noncomputable abbrev pageTwo
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    HomologicalComplex₂.First.PageTwo.entry (I.mapBicomplex F) p q ⟶
      HomologicalComplex₂.First.PageTwo.entry (J.mapBicomplex F) p q :=
  HomologicalComplex.homologyMap (pageOne f F q) p

/-- A first page-two map is the homology map induced by the corresponding page-one map. -/
@[simp]
theorem pageTwo_eq
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo f F p q = HomologicalComplex.homologyMap (pageOne f F q) p := sorry

/-- The first page-one construction preserves identity maps. -/
@[simp]
theorem pageOne_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (id I) F q = 𝟙 _ := sorry

/-- The first page-one construction preserves composition. -/
@[simp, reassoc]
theorem pageOne_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (comp f g) F q = pageOne f F q ≫ pageOne g F q := sorry

/-- The first page-one map is invertible when its mapped double-complex map is invertible. -/
instance pageOne_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ)
    [IsIso f.hom] : IsIso (pageOne f F q) := sorry

/-- The first page-two construction preserves identity maps. -/
@[simp]
theorem pageTwo_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (id I) F p q = 𝟙 _ := sorry

/-- The first page-two construction preserves composition. -/
@[simp, reassoc]
theorem pageTwo_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (comp f g) F p q = pageTwo f F p q ≫ pageTwo g F p q := sorry

/-- The first page-two map is invertible when its mapped double-complex map is invertible. -/
instance pageTwo_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ)
    [IsIso f.hom] : IsIso (pageTwo f F p q) := sorry

end First

namespace Second

/-- The induced map on the second page-one complex in horizontal homology degree `q`. -/
@[stacks 015J "second Cartan-Eilenberg page-one map"]
noncomputable abbrev pageOne
    (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    HomologicalComplex₂.Second.PageOne.complex (I.mapBicomplex F) q ⟶
      HomologicalComplex₂.Second.PageOne.complex (J.mapBicomplex F) q :=
  (CategoryTheory.CochainComplex.rescaleDifferential.functor
      (C := B) (q.negOnePow : ℤ)).map
    (((HomologicalComplex.homologyFunctor B (up ℤ) q).mapHomologicalComplex (up ℤ)).map
      ((HomologicalComplex₂.flipFunctor B (up ℤ) (up ℤ)).map (mapped f F)))

/-- The second page-one map in vertical degree `p` is the homology map induced by the
corresponding row map of the mapped double complexes. -/
@[simp]
theorem pageOne_f
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    (pageOne f F q).f p =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (up ℤ)).map (row f p)) q := sorry

/-- The induced map on a second page-two entry. -/
@[stacks 015J "second Cartan-Eilenberg page-two map"]
noncomputable abbrev pageTwo
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    HomologicalComplex₂.Second.PageTwo.entry (I.mapBicomplex F) p q ⟶
      HomologicalComplex₂.Second.PageTwo.entry (J.mapBicomplex F) p q :=
  HomologicalComplex.homologyMap (pageOne f F q) p

/-- A second page-two map is the homology map induced by the corresponding page-one map. -/
@[simp]
theorem pageTwo_eq
    (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo f F p q = HomologicalComplex.homologyMap (pageOne f F q) p := sorry

/-- The second page-one construction preserves identity maps. -/
@[simp]
theorem pageOne_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (id I) F q = 𝟙 _ := sorry

/-- The second page-one construction preserves composition. -/
@[simp, reassoc]
theorem pageOne_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    pageOne (comp f g) F q = pageOne f F q ≫ pageOne g F q := sorry

/-- The second page-one map is invertible when its mapped double-complex map is invertible. -/
instance pageOne_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ)
    [IsIso f.hom] : IsIso (pageOne f F q) := sorry

/-- The second page-two construction preserves identity maps. -/
@[simp]
theorem pageTwo_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (id I) F p q = 𝟙 _ := sorry

/-- The second page-two construction preserves composition. -/
@[simp, reassoc]
theorem pageTwo_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    pageTwo (comp f g) F p q = pageTwo f F p q ≫ pageTwo g F p q := sorry

/-- The second page-two map is invertible when its mapped double-complex map is invertible. -/
instance pageTwo_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ)
    [IsIso f.hom] : IsIso (pageTwo f F p q) := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Map
