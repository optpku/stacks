module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Precomposition

/-!
# Injective Targets for Hom-Complex Precomposition

This leaf records the exactness properties of contravariant Hom-complex
precomposition against a termwise injective cochain complex.  It is independent
of any particular resolution construction.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Precomposition on degree-`n` Hom-complex cochains is injective when the source map is
epic. -/
theorem homComplexPrecomp_injective_of_epi
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) [Epi f] (n : ℤ) :
    Function.Injective (homComplexPrecompAddMonoidHom (f := f) (I := I) n) := sorry

/-- Precomposition on degree-`n` Hom-complex cochains is surjective along a monomorphism when
the target complex has injective terms. -/
theorem homComplexPrecomp_surjective_of_mono
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) [Mono f]
    (hI : ∀ j : ℤ, Injective (I.X j)) (n : ℤ) :
    Function.Surjective (homComplexPrecompAddMonoidHom (f := f) (I := I) n) := sorry

/-- A short exact row of cochain complexes induces an exact row of fixed-degree Hom-complex
cochains against a termwise injective target. -/
theorem homComplexPrecomp_exact_of_shortExact
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (I : CochainComplex C ℤ) (hI : ∀ j : ℤ, Injective (I.X j)) (n : ℤ) :
    Function.Exact
      (homComplexPrecompAddMonoidHom (f := S.g) (I := I) n)
      (homComplexPrecompAddMonoidHom (f := S.f) (I := I) n) := sorry

/-- The two contravariant Hom-complex precomposition maps associated to a short complex compose
to zero. -/
theorem homComplexPrecomp_comp_zero
    (S : ShortComplex (CochainComplex C ℤ)) (I : CochainComplex C ℤ) :
    homComplexPrecomp (f := S.g) (I := I) ≫ homComplexPrecomp (f := S.f) (I := I) = 0 := sorry

/-- The two contravariant Hom-complex precomposition maps associated to a short complex form a
short complex. -/
noncomputable def homComplexPrecompShortComplex
    (S : ShortComplex (CochainComplex C ℤ)) (I : CochainComplex C ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat ℤ) where
  X₁ := CochainComplex.HomComplex S.X₃ I
  X₂ := CochainComplex.HomComplex S.X₂ I
  X₃ := CochainComplex.HomComplex S.X₁ I
  f := homComplexPrecomp (f := S.g) (I := I)
  g := homComplexPrecomp (f := S.f) (I := I)
  zero := homComplexPrecomp_comp_zero S I

/-- Precomposition against a termwise injective cochain complex sends a short exact row to a
short exact row of Hom complexes. -/
theorem homComplexPrecomp_shortExact_of_termwiseInjective
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (I : CochainComplex C ℤ) (hI : ∀ j : ℤ, Injective (I.X j)) :
    (homComplexPrecompShortComplex S I).ShortExact := sorry

end CategoryTheory.CochainComplex
