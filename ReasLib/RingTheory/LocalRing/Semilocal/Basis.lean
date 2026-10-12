/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import ReasLib.Algebra.Module.Basis.Jacobson
public import ReasLib.Algebra.Module.Basis.Quotient
public import ReasLib.Algebra.Module.Product.Basis
public import ReasLib.RingTheory.Spectrum.Maximal.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bases in finite semilocal extensions

This leaf owns the source-facing semilocal basis theorem while exposing the
two independent ingredients through the sibling module leaves.
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Submodule

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)]
variable [CommRing S] [Algebra R S] [Finite (MaximalSpectrum S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

/-- If the extension of the maximal ideal of an infinite-residue-field local ring is contained in
the Jacobson radical of a semilocal algebra, every spanning `R`-submodule contains an `S`-basis. -/
@[stacks 03C1 "basis contained in a spanning submodule over a semilocal algebra"]
theorem exists_basis_mem_of_span_eq_top
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank S M)) S M, ∀ i, b i ∈ N := sorry

end Submodule
