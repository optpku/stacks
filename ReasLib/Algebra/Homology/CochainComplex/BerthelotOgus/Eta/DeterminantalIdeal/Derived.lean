/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DerivedInvariance
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.DeterminantalIdeal
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Termwise
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.RingTheory.Ideal.Principal.Regular

/-!
# Derived invariance of principality for nonnegative eta determinantal ideals

A bounded-above termwise finite-free nonnegative complex is compared through its canonical
extension by zero.  Derived invariance of the integer determinantal ideal, followed by
cancellation of the visible regular power, transports principality in a fixed degree.
@stack 0GSW
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace CochainComplex.BerthelotOgus.Nat.DeterminantalIdeal

variable {A : Type u} [CommRing A]

/-- Principality of a nonnegative eta determinantal ideal is preserved by a derived
isomorphism between bounded-above termwise finite-free complexes. -/
@[stacks 0GSW "derived invariance of principality for eta determinantal ideals"]
theorem isPrincipal_of_isIsomorphic
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
    (etaDeterminantalIdeal f L i).IsPrincipal := sorry

end CochainComplex.BerthelotOgus.Nat.DeterminantalIdeal
