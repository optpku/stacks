/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Subquotients of Filtered Homological Complexes

This module constructs the quotient of two comparable filtration stages for a homological
complex of arbitrary shape.  The construction is functorial in the filtered complex.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w v u

namespace CategoryTheory.HomologicalComplex.Filtered.Subquotient

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- The filtration subquotient `F^p K / F^q K` for comparable stages `p ≤ q`. -/
@[stacks 0BKI "filtered homological-complex subquotient"]
abbrev complex (K : HomologicalComplex (FilteredObject C) c) {p q : ℤ}
    (hpq : p ≤ q) : HomologicalComplex C c :=
  cokernel (Stage.comparison K hpq)

/-- Naturality of the stage comparison used to construct a map of filtration subquotients. -/
theorem map_square {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    Stage.comparison K hpq ≫ Stage.map f p =
      Stage.map f q ≫ Stage.comparison L hpq := sorry

/-- The map of filtration subquotients induced by a filtered-complex morphism. -/
@[stacks 0BKI "map of filtered homological-complex subquotients"]
noncomputable def map {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) : complex K hpq ⟶ complex L hpq :=
  cokernel.map (Stage.comparison K hpq) (Stage.comparison L hpq)
    (Stage.map f q) (Stage.map f p) (map_square f hpq)

/-- The identity map induces the identity on every filtration subquotient. -/
@[simp]
theorem map_id (K : HomologicalComplex (FilteredObject C) c)
    {p q : ℤ} (hpq : p ≤ q) :
    map (𝟙 K) hpq = 𝟙 (complex K hpq) := sorry

/-- Maps of filtration subquotients preserve composition. -/
@[simp]
theorem map_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) {p q : ℤ} (hpq : p ≤ q) :
    map (f ≫ g) hpq = map f hpq ≫ map g hpq := sorry

/-- The functor taking a filtered homological complex to a fixed filtration subquotient. -/
@[stacks 0BKI "filtered homological-complex subquotient functor"]
noncomputable def functor {p q : ℤ} (hpq : p ≤ q) :
    HomologicalComplex (FilteredObject C) c ⥤ HomologicalComplex C c where
  obj K := complex K hpq
  map f := map f hpq
  map_id K := map_id K hpq
  map_comp f g := map_comp f g hpq

end CategoryTheory.HomologicalComplex.Filtered.Subquotient
