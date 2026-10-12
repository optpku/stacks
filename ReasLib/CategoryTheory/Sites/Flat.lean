/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Flat

/-!
# Representably flat and coflat functors

This module exposes symmetric proposition-valued views of Mathlib's canonical
`RepresentablyFlat` and `RepresentablyCoflat` classes.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)

/-- A functor is representably flat exactly when all its structured-arrow categories are
cofiltered. -/
theorem representablyFlat_iff :
    RepresentablyFlat u ↔
      ∀ d : D, IsCofiltered (StructuredArrow d u) := sorry

/-- A functor is representably coflat exactly when all its costructured-arrow categories are
filtered. -/
theorem representablyCoflat_iff :
    RepresentablyCoflat u ↔
      ∀ d : D, IsFiltered (CostructuredArrow u d) := sorry

namespace StructuredArrow

/-- A representably flat functor admits a map from every target object into an object in its
image. -/
theorem nonempty_of_representablyFlat (u : C ⥤ D) [RepresentablyFlat u] (d : D) :
    Nonempty (StructuredArrow d u) := sorry

end StructuredArrow

end CategoryTheory
