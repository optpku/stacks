/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

open IsLocalRing

/-!
# Closed fibers of finite fraction-field extensions

For a one-dimensional Noetherian local domain, this leaf collects the
closed-fiber consequences of a finite-dimensional extension of fraction
fields. The owner is `Ideal.primesOver`: the conclusions concern a selected
prime in, or the whole set of primes in, the closed fiber rather than a
particular textbook construction of that fiber.
-/

namespace Ideal.PrimesOver

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [IsLocalRing R] [IsNoetherianRing R] [Algebra R S]
variable [Algebra (FractionRing R) (FractionRing S)]
variable [IsScalarTower R (FractionRing R) (FractionRing S)]
variable [FiniteDimensional (FractionRing R) (FractionRing S)]

/-- Stacks Lemma 10.119.10 (1), tag `031F`: every prime in the closed fiber of a finite
fraction-field extension of one-dimensional local domains is maximal. -/
@[stacks 031F "(1)"]
theorem isMaximal_of_finiteFractionRing
    (hdim : ringKrullDim R = 1) (P : (maximalIdeal R).primesOver S) :
    P.1.IsMaximal := sorry
/- Proof strategy: combine the one-dimensional height bound for primes in the
closed fiber with the canonical maximality criterion for primes of height zero. -/

/-- Stacks Lemma 10.119.10 (2), tag `031F`: the closed fiber of a finite fraction-field extension
of one-dimensional local domains has finitely many prime ideals. -/
@[stacks 031F "(2)"]
theorem finite_of_finiteFractionRing
    (hdim : ringKrullDim R = 1) :
    Finite ((maximalIdeal R).primesOver S) := sorry
/- Proof strategy: derive a finite-height bound for every closed-fiber prime,
then use the finite-primes-over theorem for a Noetherian one-dimensional base. -/

/-- Stacks Lemma 10.119.10 (3), tag `031F`: the residue field of a prime in the closed fiber is
finite over the residue field of the closed point. The residue-field scalar structure remains
scoped to avoid competing global scalar paths. -/
@[stacks 031F "(3)"]
theorem residueField_finite_of_finiteFractionRing
    (hdim : ringKrullDim R = 1) (P : (maximalIdeal R).primesOver S) :
    letI : Algebra (maximalIdeal R).ResidueField P.1.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (maximalIdeal R) P.1
    Module.Finite (maximalIdeal R).ResidueField P.1.ResidueField := sorry
/- Proof strategy: apply finite generation of the residue-field fiber to the
finite closed-fiber extension, keeping the induced residue algebra scoped. -/

end Ideal.PrimesOver

namespace IsLocalRing.ResidueField

universe u v

/-- For a local homomorphism of one-dimensional Noetherian local domains with finite fraction
field extension, the induced extension of maximal-ideal residue fields is finite. This is the
local-hom specialization of the closed-fiber theorem, expressed with Mathlib's canonical local
residue-field scalar structure. -/
theorem finite_of_finiteFractionRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [Algebra R S]
    [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)]
    [FiniteDimensional (FractionRing R) (FractionRing S)] [IsLocalHom (algebraMap R S)]
    (hdim : ringKrullDim R = 1) :
    letI : Algebra (maximalIdeal R).ResidueField (maximalIdeal S).ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (maximalIdeal R) (maximalIdeal S)
    Module.Finite (maximalIdeal R).ResidueField (maximalIdeal S).ResidueField := sorry
/- Proof strategy: instantiate the previous closed-fiber residue-field result
at the maximal ideal of `S`, using `IsLocalHom` to identify the lying-over prime. -/

end IsLocalRing.ResidueField
