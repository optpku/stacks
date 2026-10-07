module

public import ReasLib.FieldTheory.GeometricRegularity.EssFiniteType
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Base change of regular ring maps

@stack 07C1
-/

open scoped TensorProduct

namespace RingHom.Regular

universe u v w

variable {R : Type u} {R' : Type v} {Λ : Type w}
variable [CommRing R] [CommRing R'] [CommRing Λ]
variable [Algebra R Λ] [Algebra R R'] [Algebra.EssFiniteType R R']

/-- Lemma 15.41.3: essentially finite type base change preserves regular ring maps. -/
@[stacks 07C1 "base change of regular ring maps"]
theorem baseChange_of_essFiniteType (h : (algebraMap R Λ).Regular) :
    (algebraMap R' (R' ⊗[R] Λ)).Regular := sorry

end RingHom.Regular
