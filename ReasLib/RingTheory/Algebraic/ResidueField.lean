/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import ReasLib.RingTheory.RingHom.Local.Properties

/-!
# Algebraic residue-field extensions

This module records algebraicity of the residue-field extensions induced by an
algebra map and its recognition from local and weakly étale hypotheses.
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An algebra induces algebraic residue-field extensions if every element of `κ(q)`
is a root of a nonzero polynomial over `κ(φ⁻¹(q))`. -/
def IsAlgebraicOnResidueFields (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∀ (q : PrimeSpectrum S) (x : q.asIdeal.ResidueField),
    ∃ p : ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)[X],
      p ≠ 0 ∧
        p.eval₂
            (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
              q.asIdeal (algebraMap R S) (PrimeSpectrum.comap_asIdeal (algebraMap R S) q))
            x = 0

namespace IsAlgebraicOnResidueFields

/-- Unfolded form of `IsAlgebraicOnResidueFields` at a prime of the target. -/
theorem apply (h : IsAlgebraicOnResidueFields R S) (q : PrimeSpectrum S)
    (x : q.asIdeal.ResidueField) :
    ∃ p : ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)[X],
      p ≠ 0 ∧
        p.eval₂
            (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
              q.asIdeal (algebraMap R S) (PrimeSpectrum.comap_asIdeal (algebraMap R S) q))
            x = 0 :=
  h q x

/-- Algebraicity of residue-field extensions at an arbitrary lying-over pair. -/
theorem spec (h : IsAlgebraicOnResidueFields R S)
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (x : P.ResidueField) :
    ∃ f : (p.ResidueField)[X],
      f ≠ 0 ∧ f.eval₂ (Ideal.ResidueField.map p P (algebraMap R S) (Ideal.over_def P p)) x = 0 :=
  sorry

/-- `IsAlgebraicOnResidueFields` is equivalent to algebraicity of `Ideal.ResidueField.map`
at every lying-over pair. -/
theorem iff :
    IsAlgebraicOnResidueFields R S ↔
      ∀ (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
        (x : P.ResidueField),
        ∃ f : (p.ResidueField)[X],
          f ≠ 0 ∧
            f.eval₂ (Ideal.ResidueField.map p P (algebraMap R S) (Ideal.over_def P p)) x = 0 :=
  sorry

/-- Weakly étale algebras induce algebraic residue-field extensions. -/
theorem of_weaklyEtale [WeaklyEtale R S] : IsAlgebraicOnResidueFields R S := sorry

/-- Local isomorphisms induce algebraic residue-field extensions. -/
theorem of_isLocalIso [IsLocalIso R S] : IsAlgebraicOnResidueFields R S := sorry

end IsAlgebraicOnResidueFields

end Algebra

namespace Algebra.IsAlgebraicOnResidueFields

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A map that identifies local rings induces algebraic residue-field extensions. -/
theorem of_isIsoOnLocalRings (h : (algebraMap R S).IsIsoOnLocalRings) :
    IsAlgebraicOnResidueFields R S := sorry

end Algebra.IsAlgebraicOnResidueFields
