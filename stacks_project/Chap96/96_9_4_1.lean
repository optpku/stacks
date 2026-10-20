/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

/- 96.9.4.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids
and let `F` be an étale sheaf of `𝒪_𝒳`-modules. If `φ : x ⟶ y` is a morphism
of `𝒳` lying over `a : U ⟶ V`, the set-valued comparison is compatible with
`a_small^♯` and induces a comparison morphism
`c_φ : a_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` of `𝒪_{U_étale}`-modules,
owned by `GroupoidsOver.moduleComparison`. -/
@[stacks 06WC] #check (AlgebraicGeometry.GroupoidsOver.moduleComparison :
  {S : Scheme.{u}} → {X : GroupoidsOver S} → {x y : X.total} →
    (φ : x ⟶ y) → (F : SheafOfModules.{u} (etaleStructureSheaf X)) →
      ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePullback.{u}).obj
          ((restrictModulesToSmallEtale X y).obj F) ⟶
        (restrictModulesToSmallEtale X x).obj F)
