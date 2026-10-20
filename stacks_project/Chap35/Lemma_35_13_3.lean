/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Surjective.UniversalEffectiveEpi
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.13.3 (1): the coproduct map of a universally effective epimorphic family of
scheme morphisms is surjective. -/
@[stacks 0EUB] #check
  (AlgebraicGeometry.Surjective.sigmaDesc_of_universalEffectiveEpiFamily :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (K : CategoryTheory.SemiRepresentableFamily.Over.{u} X)
      [CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K],
      AlgebraicGeometry.Surjective
        (CategoryTheory.Limits.Sigma.desc (fun i : K.index ↦ (K.obj i).hom)))

/- Lemma 35.13.3 (2): for a universally effective epimorphic family in the category of
affine schemes, the coproduct map of the underlying scheme morphisms is surjective. -/
@[stacks 0EUB] #check
  (AlgebraicGeometry.Surjective.sigmaDesc_forget_of_universalEffectiveEpiFamily :
    ∀ {X : AlgebraicGeometry.AffineScheme.{u}}
      (K : CategoryTheory.SemiRepresentableFamily.Over.{u} X)
      [CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K],
      AlgebraicGeometry.Surjective
        (CategoryTheory.Limits.Sigma.desc
          (fun i : K.index ↦
            AlgebraicGeometry.AffineScheme.forgetToScheme.map (K.obj i).hom)))
