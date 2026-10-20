/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.«96_9_4_1_Comparison»

/-!
# Flat base change for étale modules on an algebraic stack

An étale `𝒪_X`-module on an algebraic stack has the flat base change property
when the comparison `c_φ : f_small^*(F|_{U'_étale}) ⟶ F|_{U_étale}` is an
isomorphism whenever `φ : x ⟶ x'` lies over a flat morphism of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- An étale `𝒪_X`-module has the flat base change property if the comparison
`c_φ` is an isomorphism whenever `φ` lies over a flat morphism of schemes. -/
@[mk_iff]
class HasFlatBaseChange {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) : Prop where
  /-- The comparison `c_φ` is an isomorphism along every flat lying-over morphism. -/
  comparison_isIso : ∀ {x y : X.total} (φ : x ⟶ y),
    Flat (X.p.map φ).left → IsIso (moduleComparison φ F)

/-- Source-semantic characterisation: `c_φ` is an isomorphism whenever the
scheme morphism underlying `φ` is flat. -/
theorem hasFlatBaseChange_spec {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) :
    HasFlatBaseChange F ↔
      ∀ {x y : X.total} (φ : x ⟶ y),
        Flat (X.p.map φ).left → IsIso (moduleComparison φ F) :=
  sorry

/-- The étale structure sheaf `𝒪_X` has the flat base change property. -/
instance instHasFlatBaseChangeUnit {X : GroupoidsOver S} [AlgebraicStack X] :
    HasFlatBaseChange
      (SheafOfModules.unit (etaleStructureSheaf X) : etaleModules X) :=
  sorry

/-- The comparison `c_φ` is an isomorphism when `F` has the flat base change
property and `φ` lies over a flat morphism. -/
instance instEtaleModuleComparisonIsIso {X : GroupoidsOver S} [AlgebraicStack X]
    {F : etaleModules X} [hF : HasFlatBaseChange F] {x y : X.total}
    (φ : x ⟶ y) [hflat : Flat (X.p.map φ).left] :
    IsIso (moduleComparison φ F) :=
  hF.comparison_isIso φ hflat

/-- The object property of étale `𝒪_X`-modules with the flat base change
property. -/
abbrev hasFlatBaseChange (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (etaleModules X) :=
  HasFlatBaseChange

/-- Membership in `hasFlatBaseChange X` is the class `HasFlatBaseChange`. -/
theorem mem_hasFlatBaseChange {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) :
    hasFlatBaseChange X F ↔ HasFlatBaseChange F :=
  sorry

end AlgebraicGeometry.GroupoidsOver
