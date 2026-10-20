/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AbsoluteWeakNormalization.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 38.38.5 (1): the global-sections map induced by a functorial absolute weak
normalization presents `X ↦ Γ(awn.obj X, 𝒪)` as the sheafification of the structure
presheaf on a chosen big h site over `S`. -/
@[stacks 0EVU] #check
  (AlgebraicGeometry.AbsoluteWeakNormalization.hSheafification :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
      (awn : AlgebraicGeometry.Scheme.{u} ⥤ AlgebraicGeometry.Scheme.{u})
      (π : awn ⟶ 𝟭 AlgebraicGeometry.Scheme.{u})
      (hπ : ∀ X, AlgebraicGeometry.UniversalHomeomorphism (π.app X))
      (hawn : ∀ X, AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal (awn.obj X)),
      Presheaf.IsSheafification (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S)
        (AlgebraicGeometry.Scheme.Site.structurePresheafMap
          (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S) awn
          (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S)
          (Functor.whiskerLeft (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S) π ≫
            (Functor.rightUnitor
              (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S)).hom)))

/- Lemma 38.38.5 (2): the global-sections map induced by a functorial absolute weak
normalization presents `X ↦ Γ(awn.obj X, 𝒪)` as the sheafification of the structure
presheaf for the big ph topology over `S`. -/
@[stacks 0EVU]
#check
  (AlgebraicGeometry.AbsoluteWeakNormalization.phSheafification :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (awn : AlgebraicGeometry.Scheme.{u} ⥤ AlgebraicGeometry.Scheme.{u})
      (π : awn ⟶ 𝟭 AlgebraicGeometry.Scheme.{u})
      (hπ : ∀ X, AlgebraicGeometry.UniversalHomeomorphism (π.app X))
      (hawn : ∀ X, AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal (awn.obj X)),
      Presheaf.IsSheafification (AlgebraicGeometry.Scheme.bigPhSite S)
        (AlgebraicGeometry.Scheme.Site.structurePresheafMap (Over.forget S) awn
          (Over.forget S)
          (Functor.whiskerLeft (Over.forget S) π ≫
            (Functor.rightUnitor (Over.forget S)).hom)))
