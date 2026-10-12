/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale.Functor
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.PreservesHomology
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages

/-!
# Page-one comparisons after applying a functor

The column- and row-homology comparisons for a mapped cohomological double complex induce
comparisons on the first and second page-one complexes.  The second presentation handles the
standard `(-1)^q` rescaling once and exposes an unscaled target for downstream derived-functor
computations.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace HomologicalComplex₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

namespace Map

namespace First
namespace PageOne

/-- The first page-one complex after applying a functor is canonically the functor applied to
the vertical-homology complex of the original double complex. -/
@[stacks 015J "column homology after applying a functor"]
noncomputable def iso
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (q : ℤ)
    [∀ p : ℤ, F.PreservesLeftHomologyOf ((K.X p).sc q)] :
    First.PageOne.complex ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj K) q ≅
      (F.mapHomologicalComplex (up ℤ)).obj (First.PageOne.complex K q) :=
  Map.Column.Homology.complexIso K F q

/-- The forward first page-one comparison evaluates to the column-homology component
comparison. -/
@[simp]
theorem iso_hom_f
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (q p : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.X r).sc q)] :
    (iso K F q).hom.f p =
      (Map.Column.Homology.componentIso K F q p).hom := sorry

/-- The inverse first page-one comparison evaluates to the inverse column-homology component
comparison. -/
@[simp]
theorem iso_inv_f
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (q p : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.X r).sc q)] :
    (iso K F q).inv.f p =
      (Map.Column.Homology.componentIso K F q p).inv := sorry

end PageOne

namespace PageTwo

/-- The first page-two entry after applying a functor is the homology of the functor applied to
the vertical-homology complex of the original double complex. -/
@[stacks 015J "first-page homology after applying a functor"]
noncomputable def iso
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (p q : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.X r).sc q)] :
    First.PageTwo.entry ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj K) p q ≅
      ((F.mapHomologicalComplex (up ℤ)).obj (First.PageOne.complex K q)).homology p :=
  HomologicalComplex.homologyMapIso (PageOne.iso K F q) p

/-- The forward first page-two comparison is induced on homology by the first page-one
comparison. -/
@[simp]
theorem iso_hom
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (p q : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.X r).sc q)] :
    (iso K F p q).hom =
      HomologicalComplex.homologyMap (PageOne.iso K F q).hom p := sorry

/-- The inverse first page-two comparison is induced on homology by the inverse first page-one
comparison. -/
@[simp]
theorem iso_inv
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (p q : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.X r).sc q)] :
    (iso K F p q).inv =
      HomologicalComplex.homologyMap (PageOne.iso K F q).inv p := sorry

end PageTwo
end First

namespace Second
namespace PageOne

/-- The second page-one complex after applying a functor is canonically the functor applied to
the horizontal-homology column of the original double complex. -/
@[stacks 015J "row homology after applying a functor"]
noncomputable def iso
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (q : ℤ)
    [∀ p : ℤ, F.PreservesLeftHomologyOf ((K.flip.X p).sc q)] :
    Second.PageOne.complex ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj K) q ≅
      (F.mapHomologicalComplex (up ℤ)).obj (K.homology q) :=
  (CategoryTheory.CochainComplex.rescaleDifferential.functor
      (q.negOnePow : ℤ)).mapIso
      (Map.Row.Homology.complexIso K F q) ≪≫
    CategoryTheory.CochainComplex.rescaleDifferential.iso
      ((F.mapHomologicalComplex (up ℤ)).obj (K.homology q)) q.negOnePow

/-- The forward page-one comparison evaluates to the row-homology comparison followed by the
canonical sign-removal component. -/
@[simp]
theorem iso_hom_f
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (q p : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.flip.X r).sc q)] :
    (iso K F q).hom.f p =
      (Map.Row.Homology.componentIso K F q p).hom ≫
        (CategoryTheory.CochainComplex.rescaleDifferential.iso
          ((F.mapHomologicalComplex (up ℤ)).obj (K.homology q)) q.negOnePow).hom.f p := sorry

/-- The inverse page-one comparison first inserts the canonical sign and then applies the
inverse row-homology comparison. -/
@[simp]
theorem iso_inv_f
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (q p : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.flip.X r).sc q)] :
    (iso K F q).inv.f p =
      (CategoryTheory.CochainComplex.rescaleDifferential.iso
          ((F.mapHomologicalComplex (up ℤ)).obj (K.homology q)) q.negOnePow).inv.f p ≫
        (Map.Row.Homology.componentIso K F q p).inv := sorry

end PageOne

namespace PageTwo

/-- The second page-two entry after applying a functor is the homology of the functor applied to
the horizontal-homology column of the original double complex. -/
@[stacks 015J "second-page homology after applying a functor"]
noncomputable def iso
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (p q : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.flip.X r).sc q)] :
    Second.PageTwo.entry ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj K) p q ≅
      ((F.mapHomologicalComplex (up ℤ)).obj (K.homology q)).homology p :=
  HomologicalComplex.homologyMapIso (PageOne.iso K F q) p

/-- The forward second-page comparison is induced on homology by the page-one comparison. -/
@[simp]
theorem iso_hom
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (p q : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.flip.X r).sc q)] :
    (iso K F p q).hom =
      HomologicalComplex.homologyMap (PageOne.iso K F q).hom p := sorry

/-- The inverse second-page comparison is induced on homology by the inverse page-one
comparison. -/
@[simp]
theorem iso_inv
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (F : C ⥤ D) [F.Additive] (p q : ℤ)
    [∀ r : ℤ, F.PreservesLeftHomologyOf ((K.flip.X r).sc q)] :
    (iso K F p q).inv =
      HomologicalComplex.homologyMap (PageOne.iso K F q).inv p := sorry

end PageTwo
end Second
end Map

end HomologicalComplex₂
