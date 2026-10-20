module

public import ReasLib.RingTheory.RootsOfUnity.KummerArtinSchreier
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Polynomial
open scoped IntermediateField

universe uA uK uL

/-!
# Generators of Kummer--Artin--Schreier extensions

This leaf owns the field-theoretic consequences of a quotient-polynomial equation.  It is
independent of valuation theory: a root of the displayed degree-`p` polynomial is algebraic, and a
single such generator makes the ambient field finite-dimensional.

@stack 09F3
-/

namespace KummerArtinSchreier
namespace IsQuotient

variable {A : Type uA} [CommRing A]
variable {K : Type uK} [Field K] [Algebra A K]
variable {L : Type uL} [Field L] [Algebra K L]
variable {p : ℕ} [Fact p.Prime]
variable {ζ : A} {P : A[X]} {ξ : K}

/-- A root of a quotient polynomial is algebraic over the intermediate field. -/
@[stacks 09F3 "algebraicity of a quotient-polynomial generator"]
theorem isAlgebraic_of_generator
    (hP : IsQuotient p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ) :
    IsAlgebraic K z := sorry
-- Proof strategy: rewrite `P` with `hP.shape_eq` and form the monic polynomial over `K` obtained
-- by subtracting `C ξ`.  Primality gives `1 < p`, so all correction terms have degree below `p`.
-- The displayed equation `hz` makes this monic polynomial vanish at `z`; conclude integrality and
-- then algebraicity.

/-- A quotient-polynomial root which generates the ambient field makes that field finite-dimensional.
The generator condition is explicit so the theorem also applies to intermediate subextensions. -/
@[stacks 09F3 "finite-dimensionality from a quotient-polynomial generator"]
theorem finiteDimensional_of_generator
    (hP : IsQuotient p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := sorry
-- Proof strategy: apply `isAlgebraic_of_generator hP z hz`, convert algebraicity to integrality,
-- and use `IntermediateField.adjoin.finiteDimensional`.  Transport finite-dimensionality from
-- `K⟮z⟯` to `L` along the equivalence induced by `hgen`.

end IsQuotient

namespace RootPresentation

variable {A : Type uA} [CommRing A]
variable {K : Type uK} [Field K] [Algebra A K]
variable {L : Type uL} [Field L] [Algebra K L]
variable {p : ℕ} [Fact p.Prime]

/-- A generating root presentation supplies finite-dimensionality without requiring it as ambient
typeclass input. -/
@[stacks 09F3 "finite-dimensionality from a Kummer root presentation"]
theorem finiteDimensional (h : RootPresentation A K L p) : FiniteDimensional K L := sorry
-- Proof strategy: apply `h.isQuotient.finiteDimensional_of_generator` to the stored root `h.z`,
-- evaluation equation `h.eval_eq`, and generation equality `h.adjoin_eq_top`.

end RootPresentation

end KummerArtinSchreier
