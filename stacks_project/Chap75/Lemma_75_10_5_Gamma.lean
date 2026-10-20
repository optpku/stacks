module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Restrict
public import stacks_project.Chap75.Lemma_75_11_3_GlobalSections

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian

/-! # Compatibility checks for abelian-valued derived global sections -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedGlobalSectionsAb :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedGammaPushforwardIso :
  ∀ {S : Scheme.{u}} {W X : AlgebraicSpace S} (h : W ⟶ X) [Etale h],
    moduleDerivedPushforward h ⋙ moduleDerivedGlobalSectionsAb X ≅
      moduleDerivedGlobalSectionsAb W)
