/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap96.«96_10_3_3_Comparison»
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpaceComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Sheafification

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- 96.10.3.3: for a 2-commutative triangle of 1-morphisms of categories fibred
in groupoids over `(Sch/S)_fppf` with `𝒰`, `𝒱` represented by algebraic spaces
`U`, `V`, and `F` an étale sheaf of `𝒪_𝒳`-modules, the sheaf-level comparison
induces a comparison morphism of `𝒪_{U_étale}`-modules
`c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}`, owned by
`GroupoidsOver.moduleComparisonSpace`. -/
@[stacks 076R] #check (AlgebraicGeometry.GroupoidsOver.moduleComparisonSpace :
  ∀ {S : Scheme.{u}} {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf),
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F))
