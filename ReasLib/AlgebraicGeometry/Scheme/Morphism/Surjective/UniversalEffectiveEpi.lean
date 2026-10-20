/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.CategoryTheory.Sites.Family.UniversalEffectiveEpi

/-!
# Surjectivity of coproducts of universally effective epimorphic families

This file records surjectivity of the coproduct morphism associated to a universally
effective epimorphic family of schemes or affine schemes.
-/

@[expose] public section

open CategoryTheory

universe u

/-- The coproduct morphism of a universally effective epimorphic family of schemes is
surjective. -/
theorem AlgebraicGeometry.Surjective.sigmaDesc_of_universalEffectiveEpiFamily
    {X : AlgebraicGeometry.Scheme.{u}}
    (K : SemiRepresentableFamily.Over.{u} X)
    [SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K] :
    AlgebraicGeometry.Surjective
      (Limits.Sigma.desc (fun i : K.index ↦ (K.obj i).hom)) := sorry

/-- The coproduct morphism of the underlying schemes of a universally effective epimorphic
family of affine schemes is surjective. -/
theorem AlgebraicGeometry.Surjective.sigmaDesc_forget_of_universalEffectiveEpiFamily
    {X : AlgebraicGeometry.AffineScheme.{u}}
    (K : SemiRepresentableFamily.Over.{u} X)
    [SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K] :
    AlgebraicGeometry.Surjective (Limits.Sigma.desc
      (fun i : K.index ↦ AlgebraicGeometry.AffineScheme.forgetToScheme.map (K.obj i).hom)) := sorry
