/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.34.2: the canonical map to the relative normalization is a
quasi-compact open immersion, its structure morphism is integral, and the
original morphism is quasi-affine. -/
@[stacks 082J] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFinite_separated_normalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f],
      IsOpenImmersion (Hom.toNormalization f) ∧
        QuasiCompact (Hom.toNormalization f) ∧
        IsIntegralHom (Hom.fromNormalization f) ∧ QuasiAffine f)
