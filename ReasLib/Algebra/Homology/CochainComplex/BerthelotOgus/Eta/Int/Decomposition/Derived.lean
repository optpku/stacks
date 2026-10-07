module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DerivedInvariance
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

/-!
# Derived invariance of integer eta decomposition ideals

The degreewise decomposition ideal of a bounded termwise finite-free complex depends only on its
object in the derived category.  The theorem is stated for the canonical ideal datum, with no
chosen universal-property witness or chosen derived isomorphism.
@stack 0GSW
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace CochainComplex.BerthelotOgus.Int.Reduction.Decomposition

variable {A : Type u} [CommRing A]

/-- In one degree, principality on one bounded finite-free representative suffices for derived
invariance of the decomposition ideal. -/
theorem degreeIdeal_eq_of_isIsomorphic_at
    (f : nonZeroDivisors A)
    (K L : CochainComplex (ModuleCat A) ℤ)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree]
    (hK : CochainComplex.bounded (ModuleCat A) K)
    (hL : CochainComplex.bounded (ModuleCat A) L)
    (hKL : IsIsomorphic (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (i : ℤ) (hI : (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal) :
    degreeIdeal f K i = degreeIdeal f L i := sorry

/-- Lemma 15.97.8, Tag 0GSW: the degreewise eta decomposition ideals of bounded finite-free
complexes representing the same derived object agree. -/
@[stacks 0GSW "derived invariance of the integer eta decomposition ideal"]
theorem degreeIdeal_eq_of_isIsomorphic
    (f : nonZeroDivisors A)
    (K L : CochainComplex (ModuleCat A) ℤ)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree]
    (hK : CochainComplex.bounded (ModuleCat A) K)
    (hL : CochainComplex.bounded (ModuleCat A) L)
    (hKL : IsIsomorphic (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (hI : ∀ j : ℤ, (Int.etaDeterminantalIdeal (f : A) K j).IsPrincipal)
    (i : ℤ) : degreeIdeal f K i = degreeIdeal f L i := sorry

end CochainComplex.BerthelotOgus.Int.Reduction.Decomposition
