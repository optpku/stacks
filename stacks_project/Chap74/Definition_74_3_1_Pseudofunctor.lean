module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pseudofunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.descentPseudofunctor :
  (S : Scheme.{u}) →
    Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat.{u + 1, u + 1})
