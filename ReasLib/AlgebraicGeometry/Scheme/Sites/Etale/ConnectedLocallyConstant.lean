/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Connected.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u w

namespace CategoryTheory.Sheaf

/-- On a connected scheme, a locally constant sheaf of modules on the small étale site is
locally modeled by one fixed module on an étale covering. -/
theorem existsConstantModuleCover
    (X : Scheme.{u}) [ConnectedSpace X]
    {Λ : Type w} [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    [Sheaf.IsLocallyConstant F] :
    ∃ (M : ModuleCat.{w} Λ) (I : Type (u + 1)) (U : I → X.Etale),
      X.smallEtaleTopology.CoversTop U ∧
        ∀ i : I, Nonempty (F.over (U i) ≅
          (constantSheaf (X.smallEtaleTopology.over (U i)) (ModuleCat.{w} Λ)).obj M) := sorry

end CategoryTheory.Sheaf
