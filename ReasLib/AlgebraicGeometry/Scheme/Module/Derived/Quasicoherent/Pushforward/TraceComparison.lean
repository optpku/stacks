/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Noetherian

/-!
# Comparison of finite trace maps
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Plus
open CohomologyIn
open SheafOfModules.RingedSite
open RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical right adjoint of derived quasicoherent pushforward. -/
noncomputable abbrev finiteRightAdjoint {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : Y ⟶ X) :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  (pushforwardCohomologyIn f).rightAdjoint

/-- The adjunction associated to the canonical right adjoint of derived pushforward. -/
noncomputable def finitePushforwardAdjunction {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : Y ⟶ X) :
    pushforwardCohomologyIn f ⊣ finiteRightAdjoint f :=
  Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f)

/-- The canonical finite-morphism trace, as the canonical pushforward-adjunction
counit at the unbounded image of a bounded-below quasicoherent complex. -/
noncomputable def finiteTraceMap
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y]
    (f : Y ⟶ X) [IsFinite f] (K : Plus X) :
    (pushforwardCohomologyIn f).obj
        ((finiteRightAdjoint f).obj
          ((toUnbounded
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K)) ⟶
      (toUnbounded
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K :=
  (finitePushforwardAdjunction f).counit.app
    ((toUnbounded
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K)

/-- The map induced by `𝒪_X ⟶ f_* 𝒪_Y`, as the derived coextension-adjunction counit
at the ambient image of a bounded-below quasicoherent complex. -/
noncomputable def structureSheafInducedMap
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y]
    (f : Y ⟶ X) [IsFinite f] (K : Plus X) :
    (DerivedCoextension.restriction
        (commRingSheafPushforwardMap f.toShHom)).obj
        ((DerivedCoextension.functor
            (commRingSheafPushforwardMap f.toShHom)).obj
          ((ambient
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K)) ⟶
      (ambient
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K :=
  (DerivedCoextension.adjunction
      (commRingSheafPushforwardMap f.toShHom)).counit.app
    ((ambient
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K)

/-- For a finite morphism of Noetherian schemes, the canonical trace and the
structure-sheaf-induced map agree after an identification of their native sources
in the ambient derived category. -/
theorem finiteTrace_commutes
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y]
    (f : Y ⟶ X) [IsFinite f] (K : Plus X) :
    ∃ (e :
      ((DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).obj
          ((pushforwardCohomologyIn f).obj
            ((finiteRightAdjoint f).obj
              ((toUnbounded
                  (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))) ≅
        (DerivedCoextension.restriction
            (commRingSheafPushforwardMap f.toShHom)).obj
          ((DerivedCoextension.functor
              (commRingSheafPushforwardMap f.toShHom)).obj
            ((ambient
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))),
      e.hom ≫ structureSheafInducedMap f K =
        ((DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).map
              (finiteTraceMap f K) ≫
          (toUnbounded.compιIso
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).hom.app K := sorry

/-- For a closed immersion of Noetherian schemes, the canonical trace and the
structure-sheaf-induced map agree after an identification of their native sources
in the ambient derived category. -/
theorem closedImmersionTrace_commutes
    {X Z : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (K : Plus X) :
    ∃ (e :
      ((DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).obj
          ((pushforwardCohomologyIn i).obj
            ((finiteRightAdjoint i).obj
              ((toUnbounded
                  (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))) ≅
        (DerivedCoextension.restriction
            (commRingSheafPushforwardMap i.toShHom)).obj
          ((DerivedCoextension.functor
              (commRingSheafPushforwardMap i.toShHom)).obj
            ((ambient
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))),
      e.hom ≫ structureSheafInducedMap i K =
        ((DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).map
              (finiteTraceMap i K) ≫
          (toUnbounded.compιIso
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).hom.app K := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
