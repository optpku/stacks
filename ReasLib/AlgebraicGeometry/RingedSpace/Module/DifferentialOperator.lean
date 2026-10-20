/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential operators relative to a morphism of ringed spaces

The construction is owned on arbitrary ringed sites. This file specializes its coefficient
morphism to `f⁻¹𝒪_S ⟶ 𝒪_X` and provides the geometric notation `Diff(f ; k ; F, G)`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X S : RingedSpace.{u}}

/-- The additive-group-valued functor of order-`k` differential operators relative to
`f : X ⟶ S`, with source `F`. -/
abbrev differentialOperatorGroups (f : X ⟶ S) (F : X.Modules) (k : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  DifferentialOperators.groupFunctor (J := Opens.grothendieckTopology X)
    (inverseImageStructureSheafHomComm f) F k

/-- The additive-group-valued source-contravariant functor of order-`k` differential operators
relative to `f : X ⟶ S`, with target `G`. -/
@[stacks 0G3X "source functor of relative differential operators"]
abbrev sourceDifferentialOperatorGroups (f : X ⟶ S) (G : X.Modules) (k : ℕ) :
    X.Modulesᵒᵖ ⥤ AddCommGrpCat.{u} :=
  DifferentialOperators.sourceGroupFunctor (J := Opens.grothendieckTopology X)
    (inverseImageStructureSheafHomComm f) G k

/-- The additive-group-valued bifunctor of order-`k` differential operators relative to
`f : X ⟶ S`. -/
@[stacks 0G3X "bifunctor of relative differential operators"]
abbrev differentialOperatorGroupBifunctor (f : X ⟶ S) (k : ℕ) :
    X.Modulesᵒᵖ × X.Modules ⥤ AddCommGrpCat.{u} :=
  DifferentialOperators.groupBifunctor (J := Opens.grothendieckTopology X)
    (inverseImageStructureSheafHomComm f) k

/-- The target-covariant functor of order-`k` differential operators relative to
`f : X ⟶ S`, with source `F`. -/
abbrev differentialOperators (f : X ⟶ S) (F : X.Modules) (k : ℕ) :
    X.Modules ⥤ Type u :=
  differentialOperatorGroups f F k ⋙ CategoryTheory.forget AddCommGrpCat

/-- The source-contravariant functor of order-`k` differential operators relative to
`f : X ⟶ S`, with target `G`. -/
@[stacks 0G3X "source functor of relative differential operators"]
abbrev sourceDifferentialOperators (f : X ⟶ S) (G : X.Modules) (k : ℕ) :
    X.Modulesᵒᵖ ⥤ Type u :=
  sourceDifferentialOperatorGroups f G k ⋙ CategoryTheory.forget AddCommGrpCat

/-- The Type-valued bifunctor of order-`k` differential operators relative to
`f : X ⟶ S`. -/
@[stacks 0G3X "relative differential-operator bifunctor"]
abbrev differentialOperatorBifunctor (f : X ⟶ S) (k : ℕ) :
    X.Modulesᵒᵖ × X.Modules ⥤ Type u :=
  differentialOperatorGroupBifunctor f k ⋙ CategoryTheory.forget AddCommGrpCat

/-- Order-`k` differential operators on `X/S` from `F` to `G`. -/
@[stacks 0G3X]
abbrev DifferentialOperator (f : X ⟶ S) (k : ℕ) (F G : X.Modules) :=
  (differentialOperators f F k).obj G

end AlgebraicGeometry.RingedSpace.Hom

namespace AlgebraicGeometry

/-- Order-`k` differential operators relative to a morphism of ringed spaces. -/
scoped[AlgebraicGeometry] notation3:max "Diff(" f " ; " k " ; " F ", " G ")" =>
  RingedSpace.Hom.DifferentialOperator f k F G

end AlgebraicGeometry
