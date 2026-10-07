module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Precomposition stability for source-local properties

If a morphism property of algebraic spaces is τ-local on the source, then it is
stable under precomposition with a morphism from the generating class of τ.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/-- An fpqc-local morphism property of algebraic spaces is stable under
precomposition with flat morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_of_fpqc
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (fpqcPrecoverage S)] :
    P.RespectsLeft (@Flat S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- An fppf-local morphism property of algebraic spaces is stable under
precomposition with morphisms that are flat and locally of finite presentation. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_finitePresentation_of_fppf
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (fppfPrecoverage S)] :
    P.RespectsLeft
      ((@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        @LocallyOfFinitePresentation S) := sorry

/-- A syntomic-local morphism property of algebraic spaces is stable under
precomposition with syntomic morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_syntomic
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (AlgebraicSpace.precoverage (@Syntomic S))] :
    P.RespectsLeft (@Syntomic S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- A smooth-local morphism property of algebraic spaces is stable under
precomposition with smooth morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_smooth
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (AlgebraicSpace.precoverage (@Smooth S))] :
    P.RespectsLeft (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- An étale-local morphism property of algebraic spaces is stable under
precomposition with étale morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_etale
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource etalePrecoverage] :
    P.RespectsLeft (@Etale S : MorphismProperty (AlgebraicSpace S)) := sorry
