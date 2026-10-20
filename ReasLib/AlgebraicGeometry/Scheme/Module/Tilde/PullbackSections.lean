/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Pullback of affine module sheaves and global sections

Morphisms from the pullback of an affine module sheaf are classified by bundled module
morphisms into global sections.  This is the composite of the tilde--global-sections
adjunction and the pullback--pushforward adjunction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- Morphisms from the pullback of the affine sheaf associated to `M` are equivalent to
`R`-linear maps from `M` into global sections over the affine base. -/
noncomputable def pullbackTildeHomEquiv
    (f : X ⟶ Spec (CommRingCat.of R)) (M : ModuleCat R) (F : X.Modules) :
    ((pullback f).obj (tilde M) ⟶ F) ≃
      (M ⟶ Scheme.Hom.globalSectionsMod f F) :=
  ((tilde.adjunction (R := CommRingCat.of R)).comp
    (pullbackPushforwardAdjunction f)).homEquiv M F

/-- The morphism from a pulled-back affine module sheaf adjoint to a bundled map into global
sections. -/
noncomputable def pullbackTildeHom
    (f : X ⟶ Spec (CommRingCat.of R)) (M : ModuleCat R) (F : X.Modules)
    (ψ : M ⟶ Scheme.Hom.globalSectionsMod f F) :
    (pullback f).obj (tilde M) ⟶ F :=
  (pullbackTildeHomEquiv f M F).symm ψ

/-- Applying the pullback-tilde/global-sections adjunction to its inverse construction recovers
the original bundled map into global sections. -/
theorem pullbackTildeHom_spec
    (f : X ⟶ Spec (CommRingCat.of R)) (M : ModuleCat R) (F : X.Modules)
    (ψ : M ⟶ Scheme.Hom.globalSectionsMod f F) :
    pullbackTildeHomEquiv f M F (pullbackTildeHom f M F ψ) = ψ := sorry

end AlgebraicGeometry.Scheme.Modules
