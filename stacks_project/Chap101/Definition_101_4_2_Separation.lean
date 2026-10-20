module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap94.Lemma_94_19_1_Localization

/-!
# Separation axioms for algebraic stacks

The shared object-separation owner supplies relative and absolute separation
predicates and their diagonal and scheme-slice APIs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.IsDMOver :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)
