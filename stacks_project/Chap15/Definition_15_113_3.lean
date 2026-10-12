/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.FieldTheory.Galois.IntegralClosure
public import ReasLib.RingTheory.Ideal.Inertia
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.113.3

@stack 09EC

The decomposition and inertia groups are canonical ideal-action owners.  This source entry recalls
them directly, including the residue-action kernel characterization of inertia; it introduces no
chapter alias and installs no competing action instance.
-/

open scoped Pointwise

universe u v w

namespace Definition_15_113_3

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
variable [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/- Definition 15.113.3 (1): the decomposition group is the stabilizer of the branch ideal. -/
@[stacks 09EC "Definition 15.113.3 (1): decomposition group"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal] =>
  (MulAction.stabilizer Gal(L/K) m : Subgroup Gal(L/K))

/- Definition 15.113.3 (2): the inertia group is the canonical ideal inertia subgroup. -/
@[stacks 09EC "Definition 15.113.3 (2): inertia group"]
#check fun (m : Ideal (integralClosure A L)) [m.IsMaximal] =>
  (m.inertia Gal(L/K) : Subgroup Gal(L/K))

/- Definition 15.113.3 (2): inertia is the kernel of the decomposition action on the residue
field, expressed with Mathlib's canonical stabilizer homomorphism. -/
@[stacks 09EC "Definition 15.113.3 (2): inertia kernel characterization"]
#check (@Ideal.Quotient.ker_stabilizerHom)

/- Definition 15.113.3 (2): mapping that kernel into the ambient Galois group recovers the
ambient inertia subgroup used throughout the ramification tower. -/
@[stacks 09EC "Definition 15.113.3 (2): ambient inertia kernel characterization"]
#check (@Ideal.Quotient.map_ker_stabilizer_subtype)

end

end Definition_15_113_3
