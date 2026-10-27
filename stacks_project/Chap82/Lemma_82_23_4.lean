/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.GysinCommutativity
import StacksCheckRecall

/-! # Commutativity of Gysin maps for two invertible sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DoubleZero
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 82.23.4: For a good algebraic space over a dimension-function base,
Gysin maps of two arbitrary invertible-module sections commute after canonical
interchange of the iterated zero schemes. The degree is reindexed so that the
composites start in degree `k + 2` and end in degree `k`. -/
@[stacks 0ERC] #check (AlgebraicGeometry.AlgebraicSpace.Hom.chowGysin_comm :
    ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) (k : ℤ),
    (ChowGroup.RefinedGysin.gysin (zeroSchemeι L s ≫ f) δ
        ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s') k).comp
      (ChowGroup.RefinedGysin.gysin f δ L s (k + 1)) =
    (ChowGroup.properPushforward
        ((iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f)
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f) δ
        (swapIso L L' s s').hom
        (swapIso_hom_comp_structure f L L' s s') k).comp
      ((ChowGroup.RefinedGysin.gysin (zeroSchemeι L' s' ≫ f) δ
          ((Modules.pullback (zeroSchemeι L' s')).obj L)
          (Modules.sectionsPullback (zeroSchemeι L' s') L s) k).comp
        (ChowGroup.RefinedGysin.gysin f δ L' s' (k + 1))))
