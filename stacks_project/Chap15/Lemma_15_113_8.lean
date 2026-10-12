/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Etale
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.113.8

@stack 09EH

The reusable owners are the subgroup-level fixed-subalgebra map and etale criterion in
`integralClosure.FixedPoints`.  This chapter file is intentionally a recall surface: it does not
rebuild quotient actions, residue-field identifications, or local instance pins.
-/

namespace Lemma_15_113_8

universe u v w

open Ideal

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

/- Lemma 15.113.8 (1): the inertia-fixed subalgebra is the integral closure in the inertia-fixed
field. -/
@[stacks 09EH "Lemma 15.113.8 (1): inertia fixed subalgebra integral closure"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal] =>
  (integralClosure.FixedPoints.isIntegralClosure
      (A := A) (K := K) (L := L) (m.inertia Gal(L / K)) :
    @IsIntegralClosure
      (FixedPoints.subalgebra A (integralClosure A L) (m.inertia Gal(L / K))) A
      (IntermediateField.fixedField (m.inertia Gal(L / K))) _ _ _ _
      (integralClosure.FixedPoints.toFixedFieldAlgebra
        (A := A) (K := K) (L := L) (m.inertia Gal(L / K))))

/- Lemma 15.113.8 (2): the inertia-fixed subalgebra is etale at the contracted branch prime. -/
@[stacks 09EH "Lemma 15.113.8 (2): inertia fixed subalgebra etale"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal] =>
  (integralClosure.FixedPoints.etaleAt_inertia (A := A) (K := K) (L := L) m :
    Algebra.IsEtaleAt A
      (m.under
        (FixedPoints.subalgebra A (integralClosure A L) (m.inertia Gal(L / K)))))

end Lemma_15_113_8
