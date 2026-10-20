module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative

/-!
# Relative perfectness on algebraic spaces

The intrinsic predicates use inverse-image coefficients and exact restriction to
slices of the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.locallyFiniteTorDimensionOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      ObjectProperty (ModuleDerived X))

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPerfectRelativeTo_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X),
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f E ↔
        IsPseudoCoherent X E ∧
          AlgebraicGeometry.AlgebraicSpace.ModuleDerived.locallyFiniteTorDimensionOver f E)
