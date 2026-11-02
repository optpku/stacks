/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_retract h hL n α hα :=
    ObjectProperty.prop_of_retract
      (fun X : DerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) ↦
        X.IsMPseudoCoherent m)
      (h.map (ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom)) (hL n α hα)

/-- The left summand of a relatively `m`-pseudo-coherent biproduct is relatively
`m`-pseudo-coherent. -/
theorem left_of_biprod (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_left
    (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) hKL

/-- The right summand of a relatively `m`-pseudo-coherent biproduct is relatively
`m`-pseudo-coherent. -/
theorem right_of_biprod (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    L.IsMPseudoCoherentRelativeTo R m :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_right
    (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) hKL

/-- Lemma 15.82.8 (1): both summands of a relatively `m`-pseudo-coherent biproduct are
relatively `m`-pseudo-coherent. -/
@[stacks 0676 "(1), m-pseudo-coherent summands"]
theorem summands_of_biprod (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m ∧ L.IsMPseudoCoherentRelativeTo R m :=
  ⟨left_of_biprod K L m hKL, right_of_biprod K L m hKL⟩

end IsMPseudoCoherentRelativeTo

namespace IsPseudoCoherentRelativeTo

/-- Relatively pseudo-coherent objects are stable under retracts. -/
@[stacks 0676 "relative pseudo-coherence is stable under retracts"]
instance isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_retract h hL m :=
    ObjectProperty.prop_of_retract
      (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) h (hL m)

/-- The left summand of a relatively pseudo-coherent biproduct is relatively
pseudo-coherent. -/
theorem left_of_biprod (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_left
    (fun X : DModA ↦ X.IsPseudoCoherentRelativeTo R) hKL

/-- The right summand of a relatively pseudo-coherent biproduct is relatively
pseudo-coherent. -/
theorem right_of_biprod (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    L.IsPseudoCoherentRelativeTo R :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_right
    (fun X : DModA ↦ X.IsPseudoCoherentRelativeTo R) hKL

/-- Lemma 15.82.8 (2): both summands of a relatively pseudo-coherent biproduct are relatively
pseudo-coherent. -/
@[stacks 0676 "(2), pseudo-coherent summands"]
theorem summands_of_biprod (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R ∧ L.IsPseudoCoherentRelativeTo R :=
  ⟨left_of_biprod K L hKL, right_of_biprod K L hKL⟩

end IsPseudoCoherentRelativeTo

end CategoryTheory.DerivedCategory
