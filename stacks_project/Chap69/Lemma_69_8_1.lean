/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.Vanishing
import StacksCheckRecall

/-!
# Lemma 69.8.1

Uniform vanishing of higher direct images of quasi-coherent modules after
arbitrary base change of a quasi-compact quasi-separated morphism of algebraic
spaces with quasi-compact target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace higherDirectImage

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.8.1: let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`, with `Y` quasi-compact.
Then there exists `n : ℕ` such that for any base change `g : Y' ⟶ Y`, writing
`X'` for `Limits.pullback f g` and `f'` for `Limits.pullback.snd f g`, the higher
direct image `R^i f'_* F'` of any quasi-coherent `𝒪_X'`-module `F'` is zero for
`n ≤ i`. -/
@[stacks 073G]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage.eventually_isZero_after_baseChange :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsQuasiCompact Y],
    ∃ n : ℕ, ∀ ⦃Y' : AlgebraicSpace S⦄ (g : Y' ⟶ Y)
      [Abelian (Limits.pullback f g).Modules] [Abelian Y'.Modules]
      [HasInjectiveResolutions (Limits.pullback f g).Modules]
      (F' : (Limits.pullback f g).Modules) [F'.IsQuasicoherent] (i : ℕ),
      n ≤ i → IsZero (higherDirectImage (Limits.pullback.snd f g) F' i))

/- Uniform vanishing of higher direct images of quasi-coherent modules after an
arbitrary cartesian base change of a quasi-compact quasi-separated morphism with
quasi-compact target. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage.eventually_isZero_of_isPullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsQuasiCompact Y],
    ∃ n : ℕ, ∀ ⦃Y' X' : AlgebraicSpace S⦄ {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {h : X' ⟶ X}
      (h_cart : IsPullback h f' f g)
      [Abelian X'.Modules] [Abelian Y'.Modules] [HasInjectiveResolutions X'.Modules]
      (F' : X'.Modules) [F'.IsQuasicoherent] (i : ℕ),
      n ≤ i → IsZero (higherDirectImage f' F' i))

end higherDirectImage

end AlgebraicGeometry.AlgebraicSpace.Modules
