module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sequential

/-!
# Complexes of modules over a sequential ring system

@stack 091D

Stage evaluation of varying-ring modules preserves zero morphisms, hence acts on homological
complexes of every shape.  This file owns that shape-polymorphic lift and its cochain
specialization.
-/

@[expose] public section

open CategoryTheory ComplexShape Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem

/-- Stage evaluation lifted to homological complexes of shape `c`. -/
@[stacks 091D "stage evaluation of homological complexes"]
abbrev complexEvaluation
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ)
    {ι : Type w} (c : ComplexShape ι) :
    HomologicalComplex (ModuleSystem.{u, v} F) c ⥤
      HomologicalComplex (ModuleCat.{v} ((ringSystemAsRingCat F).obj (op n))) c :=
  (evaluation F n).mapHomologicalComplex c

/-- The successor transition between stage evaluations of homological complexes. -/
@[stacks 091D "successor transition on homological complexes"]
abbrev complexEvaluationStep
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ)
    {ι : Type w} (c : ComplexShape ι) :
    complexEvaluation.{u, v, w} F (n + 1) c ⟶
      complexEvaluation.{u, v, w} F n c ⋙
        (ModuleCat.restrictScalars (F.stepMap n).hom).mapHomologicalComplex c :=
  NatTrans.mapHomologicalComplex (evaluationStep F n) c

/-- Stage evaluation specialized to cochain complexes indexed by `ℤ`. -/
@[stacks 091D "stage evaluation of cochain complexes"]
abbrev cochainEvaluation
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    CochainComplex (ModuleSystem.{u, v} F) ℤ ⥤
      CochainComplex (ModuleCat.{v} ((ringSystemAsRingCat F).obj (op n))) ℤ :=
  complexEvaluation F n (up ℤ)

/-- The stage-`n` cochain complex obtained by evaluation. -/
@[stacks 091D "evaluated cochain complex"]
abbrev cochainEval
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ)
    (M : CochainComplex (ModuleSystem.{u, v} F) ℤ) :
    CochainComplex (ModuleCat.{v} ((ringSystemAsRingCat F).obj (op n))) ℤ :=
  (cochainEvaluation F n).obj M

/-- The successor transition between stage evaluations of cochain complexes. -/
@[stacks 091D "successor transition on cochain complexes"]
abbrev cochainEvaluationStep
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    cochainEvaluation.{u, v} F (n + 1) ⟶
      cochainEvaluation.{u, v} F n ⋙
        (ModuleCat.restrictScalars (F.stepMap n).hom).mapHomologicalComplex (up ℤ) :=
  complexEvaluationStep F n (up ℤ)

/-- Source-facing cochain evaluation for a family `A` with successor maps `ρ`. -/
@[stacks 091D "source-facing cochain evaluation"]
abbrev sequentialRingedModuleCochainEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    CochainComplex (SeqRingMod.{u, v} A ρ) ℤ ⥤
      CochainComplex (ModuleCat.{v} (A n)) ℤ :=
  cochainEvaluation (sequentialRingSystem A ρ) n

/-- Source-facing stage-`n` evaluation of a cochain complex over `A` and `ρ`. -/
@[stacks 091D "source-facing evaluated cochain complex"]
abbrev sequentialRingedModuleCochainEval
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ)
    (M : CochainComplex (SeqRingMod.{u, v} A ρ) ℤ) :
    CochainComplex (ModuleCat.{v} (A n)) ℤ :=
  (sequentialRingedModuleCochainEvaluation A ρ n).obj M

/-- Source-facing successor transition on evaluated cochain complexes. -/
@[stacks 091D "source-facing successor transition on cochain complexes"]
abbrev sequentialRingedModuleCochainEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    sequentialRingedModuleCochainEvaluation.{u, v} A ρ (n + 1) ⟶
      sequentialRingedModuleCochainEvaluation.{u, v} A ρ n ⋙
        (ModuleCat.restrictScalars
          ((sequentialRingSystem A ρ).stepMap n).hom).mapHomologicalComplex (up ℤ) :=
  cochainEvaluationStep (sequentialRingSystem A ρ) n

end CategoryTheory.SequentialInverseSystem

end
