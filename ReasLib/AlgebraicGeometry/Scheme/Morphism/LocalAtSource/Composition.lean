module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/-- An fpqc-local morphism property is stable under precomposition with flat morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_of_fpqc
    {P : MorphismProperty Scheme.{u}} [P.IsLocalAtSource Scheme.fpqcPrecoverage] :
    P.RespectsLeft (@Flat : MorphismProperty Scheme.{u}) := sorry

/-- An fppf-local morphism property is stable under precomposition with flat morphisms
that are locally of finite presentation. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_finitePresentation_of_fppf
    {P : MorphismProperty Scheme.{u}} [P.IsLocalAtSource Scheme.fppfPrecoverage] :
    P.RespectsLeft
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) := sorry

/-- A syntomic-local morphism property is stable under precomposition with syntomic morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_syntomic
    {P : MorphismProperty Scheme.{u}} [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage] :
    P.RespectsLeft (@Syntomic : MorphismProperty Scheme.{u}) := sorry

/-- A smooth-local morphism property is stable under precomposition with smooth morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_smooth
    {P : MorphismProperty Scheme.{u}} [P.IsLocalAtSource Scheme.bigSmoothPrecoverage] :
    P.RespectsLeft (@Smooth : MorphismProperty Scheme.{u}) := sorry

/-- An étale-local morphism property is stable under precomposition with étale morphisms. -/
instance CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_etale
    {P : MorphismProperty Scheme.{u}} [P.IsLocalAtSource Scheme.etalePrecoverage] :
    P.RespectsLeft (@Etale : MorphismProperty Scheme.{u}) := sorry

/-- A Zariski-local morphism property is stable under precomposition with open immersions. -/
theorem CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_isOpenImmersion_of_zariski
    {P : MorphismProperty Scheme.{u}} [P.IsLocalAtSource Scheme.zariskiPrecoverage] :
    P.RespectsLeft (@IsOpenImmersion : MorphismProperty Scheme.{u}) := sorry
