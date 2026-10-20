module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_26_1_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.EtaleLocal

/-! # Étale-local characterizations of derived quasi-coherence -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.iff_forallAffine :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X),
    derivedQuasiCoherentModuleProperty X E ↔ DerivedQCoh.forallAffine E)
