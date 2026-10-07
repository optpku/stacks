module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Bezout
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite modules over Bezout domains

This leaf records the finite-free and torsion-splitting consequences of the
Bezout property.  The torsion submodule and its quotient remain the canonical
Mathlib objects; no auxiliary presentation or chosen basis is exposed.

@stack 0ASU
-/

open scoped DirectSum

universe u v

namespace Module.IsTorsionFree

/-- A finite torsion-free module over a Bezout domain is free. -/
@[stacks 0ASU "finite torsion-free modules over a Bezout domain"]
instance freeOfFiniteOfIsBezout
    {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Free R M := sorry
-- Proof strategy: choose finitely many generators and induct on their number.
-- Project the last generator onto the principal ideal determined by its
-- coefficient ideal; over a Bezout domain that ideal is free of rank at most
-- one.  Split the projection, apply the induction hypothesis to its
-- torsion-free kernel, and combine the free summands.

end Module.IsTorsionFree

namespace Submodule

/-- Lemma 15.125.8 (1): a finite submodule of a free module over a Bezout domain is free. -/
@[stacks 0ASU "Lemma 15.125.8 (1), finite submodules of free modules"]
theorem freeOfFiniteOfIsBezout
    {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Free R F]
    (N : Submodule R F) [Module.Finite R N] :
    Module.Free R N := sorry
-- Proof strategy: a finite generating set of `N` uses only finitely many
-- coordinates of a basis of `F`, so move `N` into a finite free direct summand.
-- Induct on its rank: the image under the last coordinate is a principal ideal,
-- split that free rank-at-most-one image, and recurse on the kernel.

end Submodule

namespace Module.Finite

variable {R : Type u} [CommRing R] [hDomain : IsDomain R] [hBezout : IsBezout R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The quotient of a finite module by its torsion submodule is finite free over a Bezout
domain.  Finiteness is supplied by the canonical quotient instance. -/
@[stacks 0ASU "torsion quotient freeness for finite modules"]
theorem torsionQuotientFree [Module.Finite R M] :
    Module.Free R (M ⧸ Submodule.torsion R M) := sorry
-- Proof strategy: use the canonical finite quotient instance and the standard
-- torsion-free instance on `M ⧸ Submodule.torsion R M`, then apply
-- `Module.IsTorsionFree.freeOfFiniteOfIsBezout`.

/-- A finite module over a Bezout domain splits as its torsion-free quotient and its torsion
submodule. -/
@[stacks 0ASU "torsion decomposition for finite modules"]
theorem torsionSplit [Module.Finite R M] :
    Nonempty
      (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) := sorry
-- Proof strategy: the preceding free quotient is projective, so split the
-- quotient map.  Combine a chosen section with the torsion inclusion, prove
-- that the resulting product map is bijective using the quotient kernel, and
-- turn it into a linear equivalence.

end Module.Finite

namespace Module.Finite

/-- The torsion submodule of a finite module over a Bezout domain is finite. -/
@[stacks 0ASU "finite torsion submodule over a Bezout domain"]
instance torsion
    {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (Submodule.torsion R M) := sorry
-- Proof strategy: obtain the torsion splitting from `Module.Finite.torsionSplit`.
-- Transport finite generation from `M` across the equivalence and then to the
-- second product factor.

end Module.Finite

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 15.125.8 (2), finite-free quotient clause: the quotient of a finitely presented module
by its torsion submodule is finite free over a Bezout domain. -/
@[stacks 0ASU "Lemma 15.125.8 (2), finite-free quotient clause"]
theorem torsionQuotientFree [Module.FinitePresentation R M] :
    Module.Free R (M ⧸ Submodule.torsion R M) := sorry
-- Proof strategy: obtain `Module.Finite R M` from finite presentation and apply
-- `Module.Finite.torsionQuotientFree`.

/-- Lemma 15.125.8 (3), splitting clause: a finitely presented module over a Bezout domain splits
as its torsion-free quotient and its torsion submodule. -/
@[stacks 0ASU "Lemma 15.125.8 (3), splitting clause"]
theorem torsionSplit [Module.FinitePresentation R M] :
    Nonempty
      (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) := sorry
-- Proof strategy: obtain `Module.Finite R M` from finite presentation and apply
-- `Module.Finite.torsionSplit`.

/-- Lemma 15.125.8 (4), cyclic-retract clause: the torsion submodule of a finitely presented
module over a Bezout domain is a retract of a finite direct sum of nonzero principal cyclic
quotients. -/
@[stacks 0ASU "Lemma 15.125.8 (4), cyclic-retract clause"]
theorem existsTorsionCyclicRetract
    [Module.FinitePresentation R M] :
    ∃ (n : ℕ) (f : Fin n → R),
      (∀ i, f i ≠ 0) ∧
        ∃ (i : Submodule.torsion R M →ₗ[R]
            (⨁ j : Fin n, R ⧸ principalIdeal (f j)))
          (r : (⨁ j : Fin n, R ⧸ principalIdeal (f j)) →ₗ[R]
            Submodule.torsion R M),
            r.comp i = LinearMap.id := sorry
-- Proof strategy: apply the local cyclic-retract theorem 0ASQ to the finite
-- torsion submodule, using that maximal localizations of a Bezout domain are
-- valuation rings.  Any summand indexed by `f j = 0` is torsion-free, so its
-- map into the torsion module vanishes; discard those coordinates and retain
-- only the nonzero principal quotients while transporting the retraction.

end Module.FinitePresentation
