module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleCompletion
public import stacks_project.Chap87.Definition_87_9_9_Spf
public import stacks_project.Chap87.«87_21_2_1_Completion»

/-! # Weak-ideal completion map compatibility

Completion maps and their canonical structural morphisms are supplied by the shared library.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

#check (TopologicalRing.continuous_algebraMap :
  ∀ (B A : Type u) [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [IsTopologicalRing B], Continuous (algebraMap B (weakIdealCompletion B A)))

#check (TopologicalRing.weakIdealCompletion.map :
  ∀ {B A A' : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
    [CommRing A'] [Algebra B A'],
    (A →ₐ[B] A') → (weakIdealCompletion B A →+* weakIdealCompletion B A'))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.specHom_weakIdealCompletion :
  ∀ {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
    (hB : Spec (.of B) ⟶ S) (A : Type u) [CommRing A] [Algebra B A],
    Spec (.of (weakIdealCompletion B A)) ⟶ S)
