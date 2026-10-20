/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.30.2: the Gysin homomorphism for the zero scheme of a section of an
invertible module descends through rational equivalence to an additive map on Chow groups. -/
@[stacks 02TO] #check
  (AlgebraicGeometry.ChowGroup.gysin :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
      (k : ℤ),
      RelativeChow delta X k →+
        RelativeChow delta (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom)) (k - 1))

#check
  (AlgebraicGeometry.ChowGroup.gysin_chowClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
      (k : ℤ)
      (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction delta) k),
      AlgebraicGeometry.ChowGroup.gysin delta X ℒ s k
          (@AlgebraicGeometry.chowClass X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction delta) inferInstance k alpha) =
        Scheme.Modules.gysin X.hom delta ℒ s (k - 1)
          (CycleGroup.reindex (X.hom.relativeDimensionFunction delta)
            (Int.sub_add_cancel k 1).symm alpha))
