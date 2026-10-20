/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.RelativeEulerCharacteristic
import StacksCheckRecall

/-!
# Lemma 72.17.2

The Euler characteristic of coherent modules on an algebraic space proper
over a field is additive along short exact sequences.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- 0DN2::statement_repair::1 — Lemma 72.17.2: let `k` be a field, let `X` be a proper algebraic space over `k`,
and let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of coherent `𝒪_X`-modules.
Then `χ(X, F₂) = χ(X, F₁) + χ(X, F₃)`. The source SES is packaged as
`C : ShortComplex X.Modules` with `hC : C.ShortExact` and `Fᵢ = C.Xᵢ`. -/
@[stacks 0DN2] #check (AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic_eq_add_of_shortExact :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)] [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] {C : ShortComplex X.Modules}
    [C.X₁.IsCoherent] [C.X₂.IsCoherent] [C.X₃.IsCoherent]
    (hC : C.ShortExact),
    eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X) C.X₂ =
      eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X) C.X₁ +
        eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X) C.X₃)

end AlgebraicGeometry.AlgebraicSpace
