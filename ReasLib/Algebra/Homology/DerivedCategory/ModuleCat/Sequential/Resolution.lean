module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sequential.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sequential.HomologicalComplex
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representatives over sequential varying-ring systems

@stack 091F
@stack 091G

This file owns cochain representatives of derived objects in a sequential varying-ring module
category with controlled transition maps or controlled stagewise K-flatness.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u

namespace CategoryTheory.SequentialInverseSystem.ModuleSystem

-- Local instance justification (instance diamond): these existence statements use the standard
-- derived category of the Grothendieck-abelian varying-ring module category; no model is exported.
attribute [local instance] HasDerivedCategory.standard

/-- Lemma 15.88.7 (091F): every derived varying-ring module has a cochain representative whose
successor maps are epimorphisms after stage evaluation. -/
@[stacks 091F "representative with epimorphic stage transitions"]
theorem existsCochainRepresentativeWithEpiTransitions
    (F : SequentialInverseSystem CommRingCat.{u})
    (K : DerivedCategory (SequentialInverseSystem.ModuleSystem.{u, u} F)) :
    ∃ (M : CochainComplex (SequentialInverseSystem.ModuleSystem.{u, u} F) ℤ)
      (e : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ, Epi ((SequentialInverseSystem.cochainEvaluationStep F n).app M) := sorry

/-- Lemma 15.88.8 (091G): every derived varying-ring module has a cochain representative whose
stage evaluations are K-flat. -/
@[stacks 091G "representative with stagewise K-flat evaluations"]
theorem existsCochainRepresentativeWithStagewiseKFlat
    {A : ℕ → Type u} [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n)
    (K : DerivedCategory (SequentialInverseSystem.SeqRingMod.{u, u} A ρ)) :
    ∃ (M : CochainComplex (SequentialInverseSystem.SeqRingMod.{u, u} A ρ) ℤ)
      (e : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ,
        (SequentialInverseSystem.sequentialRingedModuleCochainEval A ρ n M).IsKFlat := sorry

end CategoryTheory.SequentialInverseSystem.ModuleSystem
