module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.StalkRepresentation
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.UnderlyingModule
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.YonedaComparison
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.StalkRepresentation.functor :
  {X : Scheme.{u}} → [ConnectedSpace X] →
  (Λ : Type (u + 1)) → [Ring Λ] → (xbar : GeometricPoint X) → [Finite Λ] →
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] →
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat Λ
      (Aut (GeometricPoint.finiteFiber xbar)))
