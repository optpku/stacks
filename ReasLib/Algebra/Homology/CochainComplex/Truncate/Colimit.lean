/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe u

namespace CochainComplex.truncate

variable {A : Type u} [CommRing A]

/-- Evaluation after cochain truncation is naturally isomorphic to evaluation one degree
higher. -/
noncomputable def compEvalIso (p : ℕ) :
    CochainComplex.truncate ⋙
        HomologicalComplex.eval (ModuleCat A) (up ℕ) p ≅
      HomologicalComplex.eval (ModuleCat A) (up ℕ) (p + 1) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The components of the natural isomorphism from truncated evaluation to shifted evaluation
are identity isomorphisms. -/
theorem compEvalIso_app (p : ℕ) (K : CochainComplex (ModuleCat A) ℕ) :
    (compEvalIso p).app K = Iso.refl _ := sorry

/-- Cochain truncation preserves sequential colimits. -/
noncomputable instance preservesSequentialColimits :
    PreservesColimitsOfShape ℕ
      (CochainComplex.truncate :
        CochainComplex (ModuleCat A) ℕ ⥤ CochainComplex (ModuleCat A) ℕ) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun p ↦
    preservesColimitsOfShape_of_natIso (compEvalIso p).symm)

end CochainComplex.truncate

end
