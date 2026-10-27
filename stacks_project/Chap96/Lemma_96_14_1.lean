/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.QuasicoherentRestriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 96.14.1: let `S` be a scheme, and let `X → (Sch/S)_fppf` be a category
fibred in groupoids represented by an algebraic space `F` via
`e : F.toGroupoids ≌ X`. If `ℱ` is in `LQCoh(𝒪_X)`, then the restriction
`ℱ|_{F_étale}` of 96.10.2.1, identified with `(restrictModules e).obj ℱ` as
`π_{F,*} ℱ = i_F⁻¹ ℱ`, is a quasi-coherent sheaf on `(F_étale, 𝒪_F)`. -/
@[stacks 0GQC] #check (AlgebraicGeometry.GroupoidsOver.restrictModules_isQuasicoherent :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) (ℱ : etaleModules X) [IsLocallyQuasiCoherent ℱ],
    ((restrictModules e).obj ℱ).IsQuasicoherent)
