/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs

/-!
# Base change and affine pushforward of module morphisms

Affine pushforward preserves and reflects invertibility, injectivity, surjectivity,
and vanishing of quasi-coherent module morphisms after every scheme base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X' ⟶ B) (g : X ⟶ X') [Affine g]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- Affine pushforward preserves and reflects invertibility of a quasi-coherent module
morphism after base change to any scheme over the base. -/
@[stacks 0CW8]
theorem baseChangeMap_isIso_iff_of_affine_pushforward (T : SchemeOver B) :
    IsIso (baseChangeMap (g ≫ f) T.hom u) ↔
      IsIso (baseChangeMap f T.hom ((pushforward g).map u)) :=
  sorry

/-- Affine pushforward preserves and reflects injectivity of a quasi-coherent module
morphism after base change to any scheme over the base. -/
@[stacks 0CW8]
theorem baseChangeMap_mono_iff_of_affine_pushforward (T : SchemeOver B) :
    Mono (baseChangeMap (g ≫ f) T.hom u) ↔
      Mono (baseChangeMap f T.hom ((pushforward g).map u)) :=
  sorry

/-- Affine pushforward preserves and reflects surjectivity of a quasi-coherent module
morphism after base change to any scheme over the base. -/
@[stacks 0CW8]
theorem baseChangeMap_epi_iff_of_affine_pushforward (T : SchemeOver B) :
    Epi (baseChangeMap (g ≫ f) T.hom u) ↔
      Epi (baseChangeMap f T.hom ((pushforward g).map u)) :=
  sorry

/-- Affine pushforward preserves and reflects vanishing of a quasi-coherent module
morphism after base change to any scheme over the base. -/
@[stacks 0CW8]
theorem baseChangeMap_zero_iff_of_affine_pushforward (T : SchemeOver B) :
    baseChangeMap (g ≫ f) T.hom u = 0 ↔
      baseChangeMap f T.hom ((pushforward g).map u) = 0 :=
  sorry

/-- A quasi-coherent module morphism and its affine pushforward have inhabited
isomorphism functors on exactly the same schemes over the base. -/
theorem isomorphismFunctor_obj_nonempty_iff_of_affine_pushforward (T : SchemeOver B) :
    Nonempty ((isomorphismFunctor (g ≫ f) u).obj (op T)) ↔
      Nonempty ((isomorphismFunctor f ((pushforward g).map u)).obj (op T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
