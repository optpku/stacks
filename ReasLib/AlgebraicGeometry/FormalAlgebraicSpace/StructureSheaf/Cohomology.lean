/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.StructureSheaf
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation

/-!
# Vanishing of higher étale cohomology of the structure sheaf

On a countably indexed affine formal algebraic space, positive-degree cohomology
of a structure sheaf on the small étale site vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- If `X` is a countably indexed affine formal algebraic space,
then `H^n(X_étale, 𝒪_X) = 0` for every `n > 0`. Here `𝒪_X` is a sheaf of rings
on the small étale site whose value on each `U_red` is the inverse-limit ring of
stage global sections of a directed affine thickening presentation of `U`. -/
theorem isZero_cohomology_structureSheaf (X : (Over S)ᵒᵖ ⥤ Type u)
    [AffineFormalAlgebraicSpace.IsCountablyIndexedAffine X] [Reduction X]
    (𝒪 : Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) RingCat.{u})
    [IsStructureSheaf 𝒪] (n : ℕ) (hn : 0 < n)
    [HasSheafify (AlgebraicSpace.smallEtaleTopology (reduction X)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) AddCommGrpCat.{u})] :
    IsZero
      ((Sheaf.functorH (AlgebraicSpace.smallEtaleTopology (reduction X)) n).obj
        ((sheafCompose (AlgebraicSpace.smallEtaleTopology (reduction X))
            (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj 𝒪)) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
