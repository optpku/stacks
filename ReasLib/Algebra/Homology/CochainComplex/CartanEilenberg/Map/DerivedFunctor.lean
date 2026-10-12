/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.PagesFunctor
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived

/-!
# Derived target functors for Cartan--Eilenberg pages

This leaf packages the right-derived targets of the two initial-page comparisons as functors on
bundled Cartan--Eilenberg resolutions.  Its computation API lets downstream users work directly
with source complexes and source maps without unfolding composite functors.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace First.Derived

/-- Apply a fixed right-derived functor termwise to the source complexes of bundled
Cartan--Eilenberg resolutions. -/
@[stacks 015J "termwise right-derived source functor"]
noncomputable abbrev complex (F : A ⥤ B) [F.Additive] (q : ℕ) :
    Bundled A ⥤ CochainComplex B ℤ :=
  source A ⋙ CochainComplex.Plus.ι A ⋙
    (F.rightDerived q).mapHomologicalComplex (up ℤ)

/-- Object computation for the termwise right-derived source functor. -/
@[simp, stacks 015J "termwise right-derived source functor"]
theorem complex_obj (F : A ⥤ B) [F.Additive] (q : ℕ) (X : Bundled A) :
    (complex F q).obj X =
      ((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj X.base.obj := sorry

/-- Morphism computation for the termwise right-derived source functor. -/
@[simp, stacks 015J "termwise right-derived source functor"]
theorem complex_map (F : A ⥤ B) [F.Additive] (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (complex F q).map f =
      ((F.rightDerived q).mapHomologicalComplex (up ℤ)).map f.base.hom := sorry

/-- Take cohomology of the termwise right-derived source complex. -/
@[stacks 015J "homology of the termwise right-derived source functor"]
noncomputable abbrev homology (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    Bundled A ⥤ B :=
  complex F q ⋙ HomologicalComplex.homologyFunctor B (up ℤ) p

/-- Object computation for the homology of the termwise right-derived source functor. -/
@[simp, stacks 015J "homology of the termwise right-derived source functor"]
theorem homology_obj (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    (X : Bundled A) :
    (homology F p q).obj X =
      HomologicalComplex.homology
        (((F.rightDerived q).mapHomologicalComplex (up ℤ)).obj X.base.obj) p := sorry

/-- Morphism computation for the homology of the termwise right-derived source functor. -/
@[simp, stacks 015J "homology of the termwise right-derived source functor"]
theorem homology_map (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (homology F p q).map f =
      HomologicalComplex.homologyMap
        (((F.rightDerived q).mapHomologicalComplex (up ℤ)).map f.base.hom) p := sorry

end First.Derived

namespace Second.Derived

/-- Apply the `p`-th right-derived functor to degree-`q` source cohomology. -/
@[stacks 015J "right-derived source-homology functor"]
noncomputable abbrev homology (F : A ⥤ B) [F.Additive]
    (p : ℕ) (q : ℤ) : Bundled A ⥤ B :=
  source A ⋙ CochainComplex.Plus.ι A ⋙
    HomologicalComplex.homologyFunctor A (up ℤ) q ⋙ F.rightDerived p

/-- Object computation for the right-derived source-homology functor. -/
@[simp, stacks 015J "right-derived source-homology functor"]
theorem homology_obj (F : A ⥤ B) [F.Additive] (p : ℕ) (q : ℤ)
    (X : Bundled A) :
    (homology F p q).obj X =
      (F.rightDerived p).obj (HomologicalComplex.homology X.base.obj q) := sorry

/-- Morphism computation for the right-derived source-homology functor. -/
@[simp, stacks 015J "right-derived source-homology functor"]
theorem homology_map (F : A ⥤ B) [F.Additive] (p : ℕ) (q : ℤ)
    {X Y : Bundled A} (f : X ⟶ Y) :
    (homology F p q).map f =
      (F.rightDerived p).map (HomologicalComplex.homologyMap f.base.hom q) := sorry

end Second.Derived

end CochainComplex.CartanEilenbergResolution.Bundled
