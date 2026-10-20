module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Triangulated
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Retracts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Retracts of relatively pseudo-coherent derived objects

Relative pseudo-coherence is stable under retracts because restriction to every polynomial
presentation preserves retract diagrams.

@stack 0676
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace CategoryTheory.DerivedCategory

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

namespace IsMPseudoCoherentRelativeTo

/-- Relatively `m`-pseudo-coherent objects are stable under retracts. -/
@[stacks 0676 "relative m-pseudo-coherence is stable under retracts"]
instance isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) := sorry

/-- The left summand of a relatively `m`-pseudo-coherent biproduct is relatively
`m`-pseudo-coherent. -/
theorem left_of_biprod (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m := sorry

/-- The right summand of a relatively `m`-pseudo-coherent biproduct is relatively
`m`-pseudo-coherent. -/
theorem right_of_biprod (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    L.IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.8 (1): both summands of a relatively `m`-pseudo-coherent biproduct are
relatively `m`-pseudo-coherent. -/
@[stacks 0676 "(1), m-pseudo-coherent summands"]
theorem summands_of_biprod (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m ∧ L.IsMPseudoCoherentRelativeTo R m := sorry

end IsMPseudoCoherentRelativeTo

namespace IsPseudoCoherentRelativeTo

/-- Relatively pseudo-coherent objects are stable under retracts. -/
@[stacks 0676 "relative pseudo-coherence is stable under retracts"]
instance isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) := sorry

/-- The left summand of a relatively pseudo-coherent biproduct is relatively
pseudo-coherent. -/
theorem left_of_biprod (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R := sorry

/-- The right summand of a relatively pseudo-coherent biproduct is relatively
pseudo-coherent. -/
theorem right_of_biprod (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    L.IsPseudoCoherentRelativeTo R := sorry

/-- Lemma 15.82.8 (2): both summands of a relatively pseudo-coherent biproduct are relatively
pseudo-coherent. -/
@[stacks 0676 "(2), pseudo-coherent summands"]
theorem summands_of_biprod (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R ∧ L.IsPseudoCoherentRelativeTo R := sorry

end IsPseudoCoherentRelativeTo

end CategoryTheory.DerivedCategory
