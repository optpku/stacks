module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Parasitic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Parasitic presheaves of modules on an algebraic stack

A presheaf of `𝒪_X`-modules on an algebraic stack is parasitic when it
vanishes on every object whose 2-Yoneda morphism from the underlying scheme
is a flat morphism of algebraic stacks.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.GroupoidsOver.IsParasitic :
  {S : AlgebraicGeometry.Scheme.{u}} →
  {X : AlgebraicGeometry.GroupoidsOver S} →
  [AlgebraicGeometry.AlgebraicStack X] →
  PresheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj → Prop)
