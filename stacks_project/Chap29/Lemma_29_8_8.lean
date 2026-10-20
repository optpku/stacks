/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.Integral
import StacksCheckRecall

/-!
# Lemma 29.8.8

Equivalent generic-point, affine-section, and stalk criteria for a dominant morphism of integral
schemes.

@stack 0CC1
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

/- Lemma 29.8.8: for a morphism of integral schemes, dominance, preservation of the generic
point, injectivity on some or every compatible pair of nonempty affine opens, and injectivity on
some or every stalk are equivalent. -/
@[stacks 0CC1] #check
  (AlgebraicGeometry.isDominant_tfae_of_isIntegral :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y],
      List.TFAE
        [ IsDominant f
        , f (genericPoint X) = genericPoint Y
        , ∃ U : NonemptyAffineOpen X, ∃ V : NonemptyAffineOpen Y,
              ∃ e :
                  ((U.1 : X.affineOpens) : X.Opens) ≤
                    (TopologicalSpace.Opens.map f.base).obj ((V.1 : Y.affineOpens) : Y.Opens),
                Function.Injective
                  (CommRingCat.Hom.hom
                    (Scheme.Hom.appLE f ((V.1 : Y.affineOpens) : Y.Opens)
                      ((U.1 : X.affineOpens) : X.Opens) e))
        , ∀ U : NonemptyAffineOpen X, ∀ V : NonemptyAffineOpen Y,
              ∀ e :
                  ((U.1 : X.affineOpens) : X.Opens) ≤
                    (TopologicalSpace.Opens.map f.base).obj ((V.1 : Y.affineOpens) : Y.Opens),
                Function.Injective
                  (CommRingCat.Hom.hom
                    (Scheme.Hom.appLE f ((V.1 : Y.affineOpens) : Y.Opens)
                      ((U.1 : X.affineOpens) : X.Opens) e))
        , ∃ x : X, Function.Injective (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f x))
        , ∀ x : X, Function.Injective (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f x))
        ])
