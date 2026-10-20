/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FlatPullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.29.9: Gysin pullback along the zero scheme of a section commutes with flat
pullback, where the first flat pullback is taken on cycles. -/
@[stacks 0B71] #check
  (AlgebraicGeometry.Scheme.Modules.gysin_flatPullback_eq_flatPullback_gysin :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (r : ℕ) [Flat f.left] [Hom.RelativeDimension f.left r]
    (ℒ : X.left.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + 1)),
    gysin X'.hom δ ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s)
        (k + (r : ℤ))
        (CycleGroup.reindex (X'.hom.relativeDimensionFunction δ)
          (add_right_comm k 1 (r : ℤ))
          (CycleGroup.flatPullback δ X' X f r (k + 1) α)) =
      @ChowGroup.flatPullback S _ δ _
        (Over.mk
          (zeroSchemeι ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫ X'.hom))
        (Over.mk (zeroSchemeι ℒ s ≫ X.hom)) _ _
        (zeroSchemePullbackOverHom f ℒ s) r
        (zeroSchemePullbackOverHom_flat f ℒ s)
        (zeroSchemePullbackOverHom_relativeDimension f r ℒ s) k
        (gysin X.hom δ ℒ s k α))

end AlgebraicGeometry.Scheme.Modules
