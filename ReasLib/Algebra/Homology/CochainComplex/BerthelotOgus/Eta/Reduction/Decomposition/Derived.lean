module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.DeterminantalIdeal.Derived
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Reduction.Decomposition

/-!
# Derived invariance of degreewise eta decomposition ideals

The decomposition ideal is attached to the canonical reduced eta pair, not to a chosen witness
of its universal property.  For bounded-above termwise finite-free complexes, it depends only on
the represented derived object whenever the relevant determinantal ideal is principal.
@stack 0GSW
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition

variable {A : Type u} [CommRing A]

/-- In a fixed degree, a derived isomorphism preserves the decomposition ideal as soon as the
determinantal ideal on one representative is principal. -/
theorem degreeIdeal_eq_of_isIsomorphic_at
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (K L : CochainComplex (ModuleCat A) ℕ)
    [CochainComplex.Nat.IsTermwiseFiniteFree K]
    [CochainComplex.Nat.IsTermwiseFiniteFree L]
    (hK : CochainComplex.Nat.IsBoundedAbove K)
    (hL : CochainComplex.Nat.IsBoundedAbove L)
    (hKL : IsIsomorphic
      ((CochainComplex.Nat.toDerived (ModuleCat A)).obj K)
      ((CochainComplex.Nat.toDerived (ModuleCat A)).obj L))
    (i : ℕ) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    degreeIdeal f K i = degreeIdeal f L i := sorry

/-- The nonnegative extension-by-zero specialization of derived invariance for degreewise eta
decomposition ideals. -/
@[stacks 0GSW "nonnegative specialization of eta decomposition invariance"]
theorem degreeIdeal_eq_of_isIsomorphic
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (K L : CochainComplex (ModuleCat A) ℕ)
    [CochainComplex.Nat.IsTermwiseFiniteFree K]
    [CochainComplex.Nat.IsTermwiseFiniteFree L]
    (hK : CochainComplex.Nat.IsBoundedAbove K)
    (hL : CochainComplex.Nat.IsBoundedAbove L)
    (hKL : IsIsomorphic
      ((CochainComplex.Nat.toDerived (ModuleCat A)).obj K)
      ((CochainComplex.Nat.toDerived (ModuleCat A)).obj L))
    (hI : ∀ j : ℕ, (etaDeterminantalIdeal f K j).IsPrincipal)
    (i : ℕ) : degreeIdeal f K i = degreeIdeal f L i := sorry

end CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition
