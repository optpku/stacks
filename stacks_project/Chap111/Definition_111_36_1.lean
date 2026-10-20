/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 111.36.1: on a scheme `X`, a sheaf `F` of `𝒪_X`-modules is quasi-coherent if
and only if for every affine open `U : X.affineOpens` the restriction of `F` along
`U.property.fromSpec : Spec Γ(X, U) ⟶ X` is of the form `tilde M` for some
`Γ(X, U)`-module `M`, equivalently `IsIso (F.restrict U.property.fromSpec).fromTildeΓ`. -/
@[stacks 029O] #check (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_forall_affineOpen_isTilde :
  ∀ {X : Scheme.{u}} (F : X.Modules),
    F.IsQuasicoherent ↔
      ∀ U : X.affineOpens, IsIso (F.restrict U.property.fromSpec).fromTildeΓ)
