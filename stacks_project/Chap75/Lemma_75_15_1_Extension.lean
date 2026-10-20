/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Extension.Support
public import stacks_project.Chap67.Remark_67_12_5_Opens

/-!
# Extending maps from supported perfect complexes on open subspaces

On a quasi-compact quasi-separated algebraic space, a map from a perfect object of
`D(𝒪_W)` supported on the preimage of a closed subset whose complement immersion is
quasi-compact extends to a map from a globally perfect object supported on that closed
subset, so that the original object is a compatible retract of the restriction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_supported_retract_extension :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (W : OpenSubspace X) [IsQuasiCompact W.X]
      (T : Closeds (Points X)) (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
      (E : DerivedQCoh X) (P : ModuleDerived W.X)
      (hP : ModuleDerived.IsPerfect P)
      (hP_support :
        ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
      (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj),
      ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
        (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
        (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
        r.i ≫ (ModuleDerived.pullback W.ι).map β = α)
