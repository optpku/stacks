module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single

/-! # Derived pullback of modules on algebraic spaces

The single-sheaf comparison and lower-cohomology edge map are owned by
`AlgebraicSpace.Module.Derived.Pullback.Single`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyPullbackComparison :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (g : Y ⟶ X)
    (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a)),
    (Modules.pullback g).obj ((DerivedCategory.homologyFunctor (Modules X) a).obj E) ⟶
      (DerivedCategory.homologyFunctor (Modules Y) a).obj ((pullback g).obj E))
