module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap74.Definition_74_3_1_Pseudofunctor

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
  (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Xᵢ f : Type (max (u + 1) v))
