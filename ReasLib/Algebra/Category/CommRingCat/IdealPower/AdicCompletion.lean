/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.IdealPower.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Opposite

universe u

namespace CategoryTheory.CommRingCat.IdealPower.Positive

variable {A : Type u} [CommRing A]

/-- The canonical map from an `I`-adic completion to the positive quotient stage `n`. -/
noncomputable def adicCompletionEvalStage (I : Ideal A) (n : ℕ) :
    CommRingCat.of (AdicCompletion I A) ⟶ stage I n :=
  CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1))

/-- The evaluation maps from an `I`-adic completion are compatible with the positive quotient
transitions. -/
theorem adicCompletionEvalStage_naturality (I : Ideal A) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of (AdicCompletion I A))).map
        (homOfLE (Nat.le_add_right n 1)).op ≫
      adicCompletionEvalStage I n =
    adicCompletionEvalStage I (n + 1) ≫
      (system I).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The cone from an `I`-adic completion to its positive ideal-power quotient system. -/
noncomputable def adicCompletionPositiveQuotientCone (I : Ideal A) :
    Cone (system I) where
  pt := CommRingCat.of (AdicCompletion I A)
  π := NatTrans.ofOpSequence
    (fun n ↦ adicCompletionEvalStage I n)
    (adicCompletionEvalStage_naturality I)

/-- The ring-homomorphism family extracted from a cone on the positive ideal-power system. -/
noncomputable def adicCompletionConeEvalFamily
    (I : Ideal A) (s : Cone (system I)) (n : ℕ) :
    (s.pt : Type u) →+* A ⧸ I ^ n :=
  match n with
  | 0 =>
    (Ideal.Quotient.factorPow I (Nat.zero_le 1)).comp
      (s.π.app (op 0)).hom
  | n' + 1 => (s.π.app (op n')).hom

/-- The ring-homomorphism family extracted from a cone is compatible with all quotient maps. -/
theorem adicCompletionConeEvalFamily_compat
    (I : Ideal A) (s : Cone (system I)) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
        (adicCompletionConeEvalFamily I s n) =
      adicCompletionConeEvalFamily I s m := sorry

/-- The universal ring homomorphism from a cone vertex to the corresponding adic completion. -/
noncomputable def adicCompletionFromPositiveQuotientCone
    (I : Ideal A) (s : Cone (system I)) :
    s.pt ⟶ CommRingCat.of (AdicCompletion I A) :=
  CommRingCat.ofHom
    (AdicCompletion.liftRingHom I
      (adicCompletionConeEvalFamily I s)
      (adicCompletionConeEvalFamily_compat I s))

/-- The `I`-adic completion is canonically the inverse limit of its positive ideal-power
quotient system. -/
noncomputable def adicCompletionLimitIso (I : Ideal A)
    [HasLimit (system I)] :
    CommRingCat.of (AdicCompletion I A) ≅ limit (system I) where
  hom := limit.lift _ (adicCompletionPositiveQuotientCone I)
  inv := adicCompletionFromPositiveQuotientCone I (limit.cone _)
  hom_inv_id := sorry
  inv_hom_id := sorry

end CategoryTheory.CommRingCat.IdealPower.Positive
