module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Comparison
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Inertia.Relative
public import stacks_project.Chap78.Definition_78_20_1_Quotient
public import stacks_project.Chap78.Lemma_78_26_1_Presentation

/-!
# Stabilizer-conjugation compatibility

Typed checks preserve the construction and comparison interfaces for existing imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

universe u

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.preInertiaComparison :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    CartesianBasedFunctor (FiberedCategoryOver.Groupoids.inertia (preQuotient G)).p
      (preQuotient (inertiaPresentation G)).p)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.inertia_preQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    (preInertiaComparison G).toBasedFunctor.IsEquivalence)
