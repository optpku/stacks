/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient
public import ReasLib.CategoryTheory.Filtration.Quotient.Preadditive
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient.Preadditive
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Subquotient.IsIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients of Filtered Complexes

This module lifts the quotient-by-a-filtration-stage functor from filtered objects to cochain
complexes and exposes the canonical map from the underlying complex to each quotient.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The functor sending a filtered cochain complex to its quotient by `F^p`.

This is the cochain-complex owner for quotient constructions.  Statements about a fixed quotient
should use `quotientFunctor p` and its object/map computations instead of rebuilding
`mapHomologicalComplex` at each use site.
-/
@[stacks 0BKI "filtered-complex quotient functor"]
noncomputable abbrev quotientFunctor (p : ℤ) :
    FilteredComplex A ⥤ CochainComplex A ℤ :=
  (FilteredObject.quotientFunctor (C := A) p).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The quotient cochain complex `K / F^p K`, computed degreewise. -/
@[stacks 0BKI "filtered-complex quotient"]
abbrev quotient (K : FilteredComplex A) (p : ℤ) : CochainComplex A ℤ :=
  (quotientFunctor p).obj K

@[simp]
theorem quotientFunctor_obj (K : FilteredComplex A) (p : ℤ) :
    (quotientFunctor p).obj K = K.quotient p := rfl

/-- The map on quotient complexes induced by a morphism of filtered complexes. -/
@[stacks 0BKI "filtered-complex quotient map"]
abbrev quotientMap {K L : FilteredComplex A} (f : K ⟶ L) (p : ℤ) :
    K.quotient p ⟶ L.quotient p :=
  (quotientFunctor p).map f

@[simp]
theorem quotientFunctor_map {K L : FilteredComplex A} (f : K ⟶ L) (p : ℤ) :
    (quotientFunctor p).map f = K.quotientMap f p := rfl

/-- The degreewise quotient projections commute with the differentials. -/
@[reassoc, stacks 0BKI "naturality of the filtered-complex quotient projection"]
theorem underlyingToQuotient_comm (K : FilteredComplex A) (p i j : ℤ)
    (_ : (ComplexShape.up ℤ).Rel i j) :
    cokernel.π ((K.X i).filtration.stage p).arrow ≫ (K.quotient p).d i j =
      K.underlying.d i j ≫ cokernel.π ((K.X j).filtration.stage p).arrow := sorry

/-- The canonical morphism from the underlying complex to the quotient `K / F^p K`. -/
@[stacks 0BKI "underlying complex to filtration quotient"]
noncomputable def underlyingToQuotient (K : FilteredComplex A) (p : ℤ) :
    K.underlying ⟶ K.quotient p where
  f n := cokernel.π ((K.X n).filtration.stage p).arrow
  comm' := underlyingToQuotient_comm K p

/-- The filtration subquotient complex `F^p K / F^q K` for `p ≤ q`. -/
@[stacks 0BKI "filtered cochain-complex subquotient"]
abbrev subquotient (K : FilteredComplex A) {p q : ℤ} (hpq : p ≤ q) :
    CochainComplex A ℤ :=
  HomologicalComplex.Filtered.Subquotient.complex K hpq

/-- The map on filtration subquotient complexes induced by a filtered-complex morphism. -/
@[stacks 0BKI "map of filtered cochain-complex subquotients"]
abbrev subquotientMap {K L : FilteredComplex A} (f : K ⟶ L)
    {p q : ℤ} (hpq : p ≤ q) : K.subquotient hpq ⟶ L.subquotient hpq :=
  HomologicalComplex.Filtered.Subquotient.map f hpq

/-- The functor taking a filtered cochain complex to a fixed filtration subquotient. -/
@[stacks 0BKI "filtered cochain-complex subquotient functor"]
abbrev subquotientFunctor {p q : ℤ} (hpq : p ≤ q) :
    FilteredComplex A ⥤ CochainComplex A ℤ :=
  HomologicalComplex.Filtered.Subquotient.functor hpq

end CategoryTheory.FilteredComplex
