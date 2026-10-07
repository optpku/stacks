module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import stacks_project.Chap90.Lemma_90_11_7_SquareZero

/-!
# Finite products of trivial square-zero extensions

The functor `Mod_R ⥤ S`-Alg/`R` sending `M` to `R[M]` preserves finite products:
the comparison `R[M × N] ⟶ R[M] ×_R R[N]` is an isomorphism, and `R[0] ≅ R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

namespace TrivSqZeroExt

/-- Lemma 90.11.7: Let `R` be an `S`-algebra. Then the functor `Mod_R ⥤ S`-Alg/`R`
sending an `R`-module `M` to the trivial square-zero extension `R[M]` preserves
finite products. -/
@[stacks 06I9]
instance overFunctor_preservesFiniteProducts :
    PreservesFiniteProducts (overFunctor S R) := sorry

/-- The comparison morphism `R[M × N] ⟶ R[M] ×_R R[N]` is an isomorphism in
`S`-Alg/`R`. -/
theorem isIso_prodComparison (M N : ModuleCat.{u} R) :
    IsIso (prodComparison (overFunctor S R) M N) := sorry

/-- The empty-product comparison `R[0] ⟶ R` is an isomorphism in `S`-Alg/`R`. -/
theorem isIso_terminalComparison :
    IsIso (terminalComparison (overFunctor S R)) := sorry

end TrivSqZeroExt
