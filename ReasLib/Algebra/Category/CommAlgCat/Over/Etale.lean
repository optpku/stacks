/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Over.Basic

/-!
# Etale commutative algebras over a fixed target

This leaf owns the category of etale commutative `R`-algebras equipped with an
`R`-algebra map to a fixed target.  It is independent of a chosen prime,
residue field, or henselization.

@stack 04GV
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CommAlgCat.Over.Etale

/-- The object property on `Over (CommAlgCat.of R T)` selecting the algebras
that are etale over `R`. -/
@[stacks 04GV "etale algebras over a target"]
abbrev property (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :
    ObjectProperty (CategoryTheory.Over (CommAlgCat.of R T)) :=
  fun A => RingHom.Etale (algebraMap R A.left)

/-- The category of etale `R`-algebras equipped with a map to the target
`R`-algebra `T`. -/
@[stacks 04GV "pointed etale algebra category"]
abbrev category (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :=
  (property R T).FullSubcategory

/-- The diagram of etale `R`-algebras over `T`, after forgetting their maps to
`T`. -/
@[stacks 04GV "pointed etale algebra diagram"]
abbrev diagram (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :=
  CategoryTheory.ObjectProperty.Over.forgetDiagram (property R T)

/-- The canonical cocone from etale `R`-algebras over `T` to `T`. -/
@[stacks 04GV "pointed etale algebra cocone"]
abbrev cocone (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :=
  CategoryTheory.ObjectProperty.Over.forgetCocone (property R T)

/-- Etale `R`-algebras equipped with a map to any fixed commutative-ring target
form a filtered category.

The field-valued specialization is the source-facing presentation by a chosen
point (and, at a residue field, by a prime with the corresponding residue-field
map).  Keeping the target only as a commutative ring makes this owner reusable
for arbitrary affine base changes and avoids baking the geometric
specialization into the category itself. -/
@[stacks 04GV "filtered pointed etale algebras"]
theorem isFiltered {R : Type u} [CommRing R]
    {T : Type v} [CommRing T] [Algebra R T] :
    IsFiltered (category R T) := sorry

/-- Typeclass form of `isFiltered` for the canonical pointed etale category. -/
@[stacks 04GV "filtered pointed etale algebras"]
instance instIsFiltered {R : Type u} [CommRing R]
    {T : Type v} [CommRing T] [Algebra R T] :
    IsFiltered (category R T) := sorry

end CommAlgCat.Over.Etale
