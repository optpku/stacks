module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
# Applying a functor to a double complex

This file names the iterated `mapHomologicalComplex` functor with the two complex shapes in their
double-complex order.  It removes repeated nested applications from downstream APIs while
retaining Mathlib's canonical termwise construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w₁ w₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- Apply a zero-morphism-preserving functor termwise to both directions of a double complex. -/
abbrev mapHomologicalComplex₂
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {I₁ : Type w₁} {I₂ : Type w₂} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ :=
  (F.mapHomologicalComplex c₂).mapHomologicalComplex c₁

end CategoryTheory.Functor
