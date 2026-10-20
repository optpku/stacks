/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Definition 111.36.6: on a locally Noetherian scheme `X`, a quasi-coherent sheaf `ℱ` of
`𝒪_X`-modules is coherent if and only if for every point `x : X` there exists an affine open
`U : X.affineOpens` containing `x` such that the restriction of `ℱ` along
`U.property.fromSpec : Spec Γ(X, U) ⟶ X` is isomorphic to `M̃` for some finite
`Γ(X, U)`-module `M`, equivalently `IsIso (ℱ.restrict U.property.fromSpec).fromTildeΓ`
together with `Module.Finite Γ(X, (U : X.Opens)) Γ(ℱ, (U : X.Opens))`. -/
@[stacks 029T] #check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_iff_exists_affineOpen_isTilde_finite :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    ℱ.IsCoherent ↔
      ∀ x : X, ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧
          IsIso (ℱ.restrict U.property.fromSpec).fromTildeΓ ∧
            Module.Finite Γ(X, (U : X.Opens)) Γ(ℱ, (U : X.Opens)))

end AlgebraicGeometry.Scheme.Modules
