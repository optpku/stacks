module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Forward
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Category.FinTopCat
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.YonedaComparison
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Trivialization
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import stacks_project.Chap58.Theorem_58_6_2
public import stacks_project.Chap59.Lemma_59_64_4
public import stacks_project.Chap59.Lemma_59_65_1_StalkRepresentation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete

universe u

#check (AlgebraicGeometry.Scheme.finiteLocallyConstant_equivalence_finitePi1Sets :
  {X : Scheme.{u}} →
  [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] →
  [ConnectedSpace X] → (xbar : GeometricPoint X) →
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ≌
    ContAction FintypeCat.{u} (Aut (GeometricPoint.finiteFiber xbar)))
