/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Unramified.LocalRing
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# A local criterion for etaleness

This leaf packages the local flatness, residue-field separability, and
maximal-ideal criterion for an algebra to be etale at a selected prime.  The
selected prime determines its contraction, so the reusable statement does not
ask consumers to supply a duplicate `LiesOver` instance.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Algebra.IsEtaleAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]

/-- Stacks 00U6: a finitely presented algebra is etale at `q` when its local
map at `q` is flat, the extended contracted prime is the maximal ideal, and
the induced residue-field extension is separable. -/
@[stacks 00U6]
theorem of_flat_of_maximalIdeal_of_separable
    (q : Ideal S) [q.IsPrime]
    (hflat :
      (Localization.localRingHom (q.under R) q (algebraMap R S) rfl).Flat)
    (hmax :
      (q.under R).map (algebraMap R (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q))
    (hsep :
      letI : Algebra (q.under R).ResidueField q.ResidueField :=
        Ideal.ResidueField.algebraOfLiesOver (q.under R) q
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField) :
    Algebra.IsEtaleAt R q := sorry

/-- The source-facing form of Stacks 00U6 keeps the prime `p` over which `q`
is localized explicit.  It is a thin bridge to the contraction-based owner
above; the explicit form is useful when flatness and the maximal-ideal
equality are already supplied at a chosen `p`. -/
@[stacks 00U6 "explicit prime-over bridge"]
theorem of_flat_over_of_maximalIdeal_of_separable
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hflat :
      (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Flat)
    (hmax :
      p.map (algebraMap R (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q))
    (hsep :
      letI : Algebra p.ResidueField q.ResidueField :=
        Ideal.ResidueField.algebraOfLiesOver p q
      Algebra.IsSeparable p.ResidueField q.ResidueField) :
    Algebra.IsEtaleAt R q := sorry

end Algebra.IsEtaleAt
