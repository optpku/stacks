/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.KeyFormula
public import ReasLib.AlgebraicGeometry.ChowGroup.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Interchange

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The Gysin homomorphisms associated to two sections of invertible modules commute
after the canonical interchange of their iterated zero schemes. -/
theorem gysin_gysin_comm
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ ℒ' : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    [Scheme.Modules.Invertible ℒ'] (s : ℒ.sections) (s' : ℒ'.sections) (k : ℤ) :
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
            (k - 1)).comp (gysin δ X ℒ' s' k)) := sorry

end AlgebraicGeometry.ChowGroup
