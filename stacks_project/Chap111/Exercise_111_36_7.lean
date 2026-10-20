/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.PrincipalOpenExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ClosedImmersionExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.PrincipalOpenExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Opens

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Exercise 111.36.7 (1): on `X = Spec R`, every quasi-coherent module `𝒢` on the open
subscheme `D(f)` is isomorphic to the restriction of some quasi-coherent module `ℱ` on `X`. -/
@[stacks 029U] #check
  (AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_basicOpen :
    ∀ {R : CommRingCat.{u}} (f : R)
      (𝒢 : ((Spec R).basicOpen ((ΓSpecIso R).inv f)).toScheme.Modules) [𝒢.IsQuasicoherent],
      ∃ ℱ : (Spec R).Modules, ℱ.IsQuasicoherent ∧
        Nonempty (ℱ.restrict (((Spec R).basicOpen ((ΓSpecIso R).inv f)).ι) ≅ 𝒢))

/- Exercise 111.36.7 (2): on `X = Spec R`, if `i : Spec (CommRingCat.of (R ⧸ I)) ⟶ X` is the
closed immersion associated to an ideal `I`, every quasi-coherent module `𝒢` on
`Spec (CommRingCat.of (R ⧸ I))` is isomorphic to `(pullback i).obj ℱ` for some quasi-coherent
module `ℱ` on `X`. This is silly because `ℱ = (pushforward i).obj 𝒢` works via the
closed-immersion counit isomorphism. -/
@[stacks 029U] #check
  (AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_pullback_closedImmersion :
    ∀ {R : CommRingCat.{u}} (I : Ideal R)
      (𝒢 : (Spec (CommRingCat.of (R ⧸ I))).Modules) [𝒢.IsQuasicoherent],
      ∃ ℱ : (Spec R).Modules, ℱ.IsQuasicoherent ∧
        Nonempty ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj ℱ ≅ 𝒢))

/- Exercise 111.36.7 (3): if `R` is Noetherian, every coherent module `𝒢` on the open subscheme
`D(f)` is isomorphic to the restriction of some coherent module `ℱ` on `Spec R`. -/
@[stacks 029U] #check
  (AlgebraicGeometry.Scheme.Modules.exists_isCoherent_restrict_basicOpen :
    ∀ {R : CommRingCat.{u}} [IsNoetherianRing R] (f : R)
      (𝒢 : ((Spec R).basicOpen ((ΓSpecIso R).inv f)).toScheme.Modules) [𝒢.IsCoherent],
      ∃ ℱ : (Spec R).Modules, ℱ.IsCoherent ∧
        Nonempty (ℱ.restrict (((Spec R).basicOpen ((ΓSpecIso R).inv f)).ι) ≅ 𝒢))

end AlgebraicGeometry.Scheme.Modules
