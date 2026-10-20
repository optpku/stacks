/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange

/-!
# Restricted derived pushforward on algebraic spaces

Ambient derived pushforward along a quasi-compact, quasi-separated morphism
restricts to the full subcategory of complexes with quasi-coherent cohomology,
and has a uniform cohomological bound after arbitrary base change when the
target is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

namespace pushforwardCohomologyIn

/-- Derived pushforward along a quasi-compact, quasi-separated morphism of algebraic
spaces preserves derived modules with quasi-coherent cohomology. -/
theorem mapsTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage
        (moduleDerivedPushforward f) :=
  sorry

end pushforwardCohomologyIn

/-- Ambient derived pushforward restricted to complexes with quasi-coherent cohomology. -/
noncomputable def pushforwardCohomologyIn {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  (derivedQuasiCoherentModuleProperty Y).lift
    (inclusion X ⋙ moduleDerivedPushforward f)
    (fun E ↦ pushforwardCohomologyIn.mapsTo f E.obj E.property)

namespace pushforwardCohomologyIn

/-- Forgetting the restricted ambient pushforward recovers ambient derived pushforward. -/
noncomputable def inclusionIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pushforwardCohomologyIn f ⋙ inclusion Y ≅
      inclusion X ⋙ moduleDerivedPushforward f :=
  (derivedQuasiCoherentModuleProperty Y).liftCompιIso
    (inclusion X ⋙ moduleDerivedPushforward f)
    (fun E ↦ mapsTo f E.obj E.property)

/-- Over a quasi-compact algebraic space, derived pushforward along a quasi-compact and
quasi-separated morphism has a uniform upper cohomological bound on complexes whose
positive cohomology vanishes. -/
theorem uniformUpperBound {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsQuasiCompact Y] :
    ∃ N : ℤ, ∀ E : DerivedQCoh X,
      E.obj.IsLE 0 → ((pushforwardCohomologyIn f).obj E).obj.IsLE (N - 1) :=
  sorry

/-- Over a quasi-compact target, the upper cohomological bound for derived pushforward
along a quasi-compact and quasi-separated morphism can be chosen uniformly after every
base change. -/
theorem baseChangeUpperBound {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsQuasiCompact Y] :
    ∃ N : ℤ, ∀ ⦃Y' : AlgebraicSpace S⦄ (g : Y' ⟶ Y)
      (E : DerivedQCoh (pullback f g)),
      E.obj.IsLE 0 →
        ((pushforwardCohomologyIn (pullback.snd f g)).obj E).obj.IsLE (N - 1) :=
  sorry

end pushforwardCohomologyIn

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
