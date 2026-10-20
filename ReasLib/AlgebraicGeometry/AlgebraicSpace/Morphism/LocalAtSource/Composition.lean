module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Precomposition stability for source-local properties

If a morphism property of algebraic spaces is τ-local on the source, then it is
stable under precomposition with a morphism from the generating class of τ.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An fpqc-local morphism property of algebraic spaces is stable under
precomposition with flat morphisms. -/
instance respectsLeft_flat_of_fpqc
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (fpqcPrecoverage S)] :
    P.RespectsLeft (@Flat S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- An fppf-local morphism property of algebraic spaces is stable under
precomposition with morphisms that are flat and locally of finite presentation. -/
instance respectsLeft_flat_finitePresentation_of_fppf
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (fppfPrecoverage S)] :
    P.RespectsLeft
      ((@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        @LocallyOfFinitePresentation S) := sorry

/-- A syntomic-local morphism property of algebraic spaces is stable under
precomposition with syntomic morphisms. -/
instance respectsLeft_syntomic
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (AlgebraicSpace.precoverage (@Syntomic S))] :
    P.RespectsLeft (@Syntomic S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- A smooth-local morphism property of algebraic spaces is stable under
precomposition with smooth morphisms. -/
instance respectsLeft_smooth
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource (AlgebraicSpace.precoverage (@Smooth S))] :
    P.RespectsLeft (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- An étale-local morphism property of algebraic spaces is stable under
precomposition with étale morphisms. -/
instance respectsLeft_etale
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsLocalAtSource etalePrecoverage] :
    P.RespectsLeft (@Etale S : MorphismProperty (AlgebraicSpace S)) := sorry

end AlgebraicGeometry.AlgebraicSpace
