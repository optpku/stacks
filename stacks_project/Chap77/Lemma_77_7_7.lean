/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.AffinePushforward
import StacksCheckRecall

/-!
# Lemma 77.7.7

In Situation 77.7.1, an affine morphism `g : X ⟶ X'` over `B` does not change the
flattening functors of a morphism `u` of quasi-coherent modules on `Sch/B`: the
isomorphism, injectivity, surjectivity, and vanishing functors for `u` agree with
the corresponding functors for `(pushforward g).map u`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X' ⟶ B) (g : X ⟶ X') [Affine g]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/- Lemma 77.7.7 (1): Affine pushforward preserves the isomorphism locus. -/
@[stacks 0CW8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_isIso_iff_of_affine_pushforward f g u :
    ∀ (T : SchemeOver B),
    IsIso (baseChangeMap (g ≫ f) T.hom u) ↔
      IsIso (baseChangeMap f T.hom ((pushforward g).map u)))

/- Lemma 77.7.7 (2): Affine pushforward preserves the injectivity locus. -/
@[stacks 0CW8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_mono_iff_of_affine_pushforward f g u :
    ∀ (T : SchemeOver B),
    Mono (baseChangeMap (g ≫ f) T.hom u) ↔
      Mono (baseChangeMap f T.hom ((pushforward g).map u)))

/- Lemma 77.7.7 (3): Affine pushforward preserves the surjectivity locus. -/
@[stacks 0CW8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_epi_iff_of_affine_pushforward f g u :
    ∀ (T : SchemeOver B),
    Epi (baseChangeMap (g ≫ f) T.hom u) ↔
      Epi (baseChangeMap f T.hom ((pushforward g).map u)))

/- Lemma 77.7.7 (4): Affine pushforward preserves the vanishing locus. -/
@[stacks 0CW8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_zero_iff_of_affine_pushforward f g u :
    ∀ (T : SchemeOver B),
    baseChangeMap (g ≫ f) T.hom u = 0 ↔
      baseChangeMap f T.hom ((pushforward g).map u) = 0)

-- The corresponding isomorphism functors are inhabited on the same test schemes.
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_obj_nonempty_iff_of_affine_pushforward
    f g u : ∀ (T : SchemeOver B),
    Nonempty ((isomorphismFunctor (g ≫ f) u).obj (op T)) ↔
      Nonempty ((isomorphismFunctor f ((pushforward g).map u)).obj (op T)))

end AlgebraicGeometry.AlgebraicSpace.Modules
