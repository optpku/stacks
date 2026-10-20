module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Finite products of square-zero extensions over an algebra

The square-zero extension functor preserves the binary and empty products of
modules over a commutative algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

namespace TrivSqZeroExt

/-- The canonical product comparison `R[M × N] ⟶ R[M] ×_R R[N]` is an isomorphism. -/
instance isIso_prodComparison (M N : ModuleCat.{u} R) :
    IsIso (prodComparison (overFunctor S R) M N) := sorry

/-- The canonical empty-product comparison `R[0] ⟶ R` is an isomorphism. -/
instance isIso_terminalComparison :
    IsIso (terminalComparison (overFunctor S R)) := sorry

/-- The square-zero extension functor from `R`-modules to `S`-algebras over `R`
preserves all finite products. -/
instance overFunctor_preservesFiniteProducts :
    PreservesFiniteProducts (overFunctor S R) := sorry

end TrivSqZeroExt
