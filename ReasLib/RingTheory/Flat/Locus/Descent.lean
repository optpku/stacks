/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.Fiber
public import ReasLib.RingTheory.Flat.Locus.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of closed-subset flatness loci

This file owns local flatness descent along a tensor-product square and the induced descent of a
closed-subset flatness condition.

@stack 05LL
@stack 05LS
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u v w x

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

-- Local instance justification (instance diamond): select the canonical target-side algebra
-- structure on the tensor-product base change.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

namespace Module.Flat

/-- Local flatness of the tensor-base-changed module descends at a tensor prime when the target
base localization is flat over the source. -/
@[stacks 05LL "localized flatness descent through tensor base change"]
theorem localized_of_tensorBaseChange
    (q' : PrimeSpectrum S')
    (hflat_q' : Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M'))
    (hflat_p' : Module.Flat R
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap R' S') q').asIdeal R')) :
    Module.Flat R
      (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap S S') q').asIdeal M) := sorry

end Module.Flat

namespace Ideal.FlatLocus

/-- Lemma 15.18.2: the closed-fiber flatness condition descends from a tensor-product base change
when the relevant closed subset maps surjectively and the target is locally flat over the source
there. -/
@[stacks 05LL "Lemma 15.18.2"]
theorem tensorBaseChange_descends {I : Ideal R} {I' : Ideal R'}
    (hI' : Ideal.map (algebraMap R R') I ≤ I')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R R'))
      (zeroLocus (I' : Set R')) (zeroLocus (I : Set R)))
    (hlocFlat : zeroLocus (I' : Set R') ⊆ Module.flatOverBaseLocus R R' R')
    (hbase : zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
      Module.flatOverBaseLocus R' S' M') :
    zeroLocus (Ideal.map (algebraMap R S) I : Set S) ⊆
      Module.flatOverBaseLocus R S M := sorry

/-- Lemma 15.19.3: the same tensor-base-change descent holds when the closed subset also contains
the extension of an ideal of the algebra. -/
@[stacks 05LS "Lemma 15.19.3"]
theorem tensorBaseChange_add_descends {I : Ideal R} {I' : Ideal R'} {J : Ideal S}
    (hI' : Ideal.map (algebraMap R R') I ≤ I')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R R'))
      (zeroLocus (I' : Set R')) (zeroLocus (I : Set R)))
    (hlocFlat : zeroLocus (I' : Set R') ⊆ Module.flatOverBaseLocus R R' R')
    (hbase : zeroLocus
      ((Ideal.map (algebraMap R' S') I' + Ideal.map (algebraMap S S') J : Ideal S') : Set S') ⊆
        Module.flatOverBaseLocus R' S' M') :
    zeroLocus ((Ideal.map (algebraMap R S) I + J : Ideal S) : Set S) ⊆
      Module.flatOverBaseLocus R S M := sorry

end Ideal.FlatLocus
