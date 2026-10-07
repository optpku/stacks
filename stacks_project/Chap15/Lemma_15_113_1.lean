module

import StacksCheckRecall
public import ReasLib.FieldTheory.Galois.IntegralClosure
public import ReasLib.RingTheory.LocalRing.Integral
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Lemma 15.113.1

@stack 09EA
-/

@[expose] public section

open Ideal IsLocalRing
open scoped Pointwise

universe u v w

/-
Lemma 15.113.1 (tag 09EA): Let `A` be a discrete valuation ring with fraction
field `K`, and let `L/K` be a finite Galois extension.  The Galois group acts
transitively on the maximal ideals of `B = integralClosure A L`.

Current Stacks numbering: Lemma 15.112.1.
The source-facing finite-DVR specialization below intentionally retains the
finite-dimensional hypothesis; the reusable orbit theorem itself is more
general and lives in `integralClosure.exists_smul_eq_of_under_eq`.
-/

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
variable [IsScalarTower A K L] [IsGalois K L] [FiniteDimensional K L]

@[stacks 09EA "Lemma 15.113.1"]
#check fun (m m' : Ideal (integralClosure A L)) [m.IsMaximal] [m'.IsMaximal] ↦
  (integralClosure.exists_smul_eq_of_under_eq (K := K) m m'
    ((m.over_def (maximalIdeal A)).symm.trans (m'.over_def (maximalIdeal A))) :
    ∃ σ : Gal(L/K), σ • m = m')

end
