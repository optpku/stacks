/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import ReasLib.CategoryTheory.Sites.Family.Sheaf
public import ReasLib.CategoryTheory.Sites.Family.UniversalEffectiveEpi

/-!
# Quasicoherent section descent on affine schemes

This file relates the family sheaf condition for sections of pulled-back quasicoherent modules
to universal effective epimorphy of affine-scheme families.
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.AffineScheme

open CategoryTheory Scheme.Modules

/-- Quasicoherent modules have section descent for `K` when their pullback-sections presheaves
satisfy the family sheaf condition along the underlying scheme morphisms over `X`. -/
def HasQuasicoherentSectionDescent (X : AffineScheme.{u})
    (K : SemiRepresentableFamily.Over.{v} X) : Prop :=
  ∀ (F : X.obj.Modules) [F.IsQuasicoherent],
    Presheaf.IsSheafForFamily
      (PullbackSections.over X.obj F ⋙ forget AddCommGrpCat.{u})
      (fun i : K.index ↦
        (Over.post AffineScheme.forgetToScheme).obj (K.obj i))
      (fun i ↦ Over.mkIdTerminal.from
        ((Over.post AffineScheme.forgetToScheme).obj (K.obj i)))

/-- A family of morphisms of affine schemes has quasicoherent section descent if and only if
it is universally effective epimorphic. -/
theorem hasQuasicoherentSectionDescent_iff_universalEffectiveEpi
    (X : AffineScheme.{u}) (K : SemiRepresentableFamily.Over.{v} X) :
    HasQuasicoherentSectionDescent X K ↔
      SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K := sorry

end AlgebraicGeometry.AffineScheme
