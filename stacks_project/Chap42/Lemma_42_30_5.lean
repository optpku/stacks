/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Commutativity

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- Lemma 42.30.5: the two iterated Gysin maps associated to sections of invertible
modules commute after the canonical identification of their iterated zero schemes. -/
@[stacks 0B73] #check
  (AlgebraicGeometry.ChowGroup.gysin_gysin_comm :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ ℒ' : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      [Scheme.Modules.Invertible ℒ'] (s : ℒ.sections) (s' : ℒ'.sections) (k : ℤ),
      (gysin δ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom))
        ((Scheme.Modules.pullback
          (Over.homMk (Scheme.zeroSchemeι ℒ s) :
            Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left).obj ℒ')
        (Scheme.Modules.sectionsPullback
          (Over.homMk (Scheme.zeroSchemeι ℒ s) :
            Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left ℒ' s') (k - 1)).comp
          (gysin δ X ℒ s k) =
        (map δ
          (Over.mk
            (Scheme.zeroSchemeι
                ((Scheme.Modules.pullback (Scheme.zeroSchemeι ℒ' s')).obj ℒ)
                (Scheme.Modules.sectionsPullback (Scheme.zeroSchemeι ℒ' s') ℒ s) ≫
              Scheme.zeroSchemeι ℒ' s' ≫ X.hom))
          (Over.mk
            (Scheme.zeroSchemeι
                ((Scheme.Modules.pullback (Scheme.zeroSchemeι ℒ s)).obj ℒ')
                (Scheme.Modules.sectionsPullback (Scheme.zeroSchemeι ℒ s) ℒ' s') ≫
              Scheme.zeroSchemeι ℒ s ≫ X.hom))
          (Scheme.DoubleZero.swapOverIso ℒ ℒ' s s').hom ((k - 1) - 1)).comp
            ((gysin δ (Over.mk (Scheme.zeroSchemeι ℒ' s' ≫ X.hom))
              ((Scheme.Modules.pullback
                (Over.homMk (Scheme.zeroSchemeι ℒ' s') :
                  Over.mk (Scheme.zeroSchemeι ℒ' s' ≫ X.hom) ⟶ X).left).obj ℒ)
              (Scheme.Modules.sectionsPullback
                (Over.homMk (Scheme.zeroSchemeι ℒ' s') :
                  Over.mk (Scheme.zeroSchemeι ℒ' s' ≫ X.hom) ⟶ X).left ℒ s)
              (k - 1)).comp (gysin δ X ℒ' s' k)))

end AlgebraicGeometry.ChowGroup
