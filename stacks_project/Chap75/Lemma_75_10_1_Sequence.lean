module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Lemma_75_10_6_LowerShriek
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-! # Mayer–Vietoris lower-shriek constructions

The comparison maps and their cochain and derived constructions are provided by
the shared module owners. The imports also expose restriction and gluing APIs.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.fiberHom :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X),
    Limits.pullback j f ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisLowerShriekδ :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
      (DerivedCategory.Q.objPreimage E)).ShortExact),
    E ⟶ ((lowerShriekDerived (fiberHom j f)).obj
      ((restrictFunctorDerived (fiberHom j f)).obj E))⟦(1 : ℤ)⟧)
