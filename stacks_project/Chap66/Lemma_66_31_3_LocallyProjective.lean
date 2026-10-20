/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective

/-!
# Locally projective modules on algebraic spaces

The local-projectivity predicate, section modules, and étale restriction criteria are
provided by the mathematical owner imported above.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.structureRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X), RingCat)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.structureRing_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X),
    structureRing U = RingCat.of Γ(U.left.left, ⊤))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionModule :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules) (U : smallEtaleSite X),
    ModuleCat (structureRing U))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionModule_val :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules) (U : smallEtaleSite X),
    sectionModule ℱ U = ℱ.val.obj (op U))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isLocallyProjective_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules),
    IsLocallyProjective ℱ ↔
      ∀ U : affineEtaleSite X,
        Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective.of_affineEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ℱ : X.Modules},
    (∀ U : affineEtaleSite X,
      Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj)) →
        IsLocallyProjective ℱ)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective.projective_sections :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules) [IsLocallyProjective ℱ]
    (U : smallEtaleSite X) [IsAffine U.left.left],
    Module.Projective (structureRing U) (sectionModule ℱ U))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.instProjectiveAffineEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules) [IsLocallyProjective ℱ]
    (U : affineEtaleSite X),
    Module.Projective (structureRing U.obj) (sectionModule ℱ U.obj))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.instIsLocallyProjective_unit :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    IsLocallyProjective (SheafOfModules.unit (structureSheaf X) : X.Modules))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictEtale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (𝒢 : Y.Modules) (f : X ⟶ Y)
    (hf : Etale f), X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictEtale_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (𝒢 : Y.Modules) (f : X ⟶ Y)
    [hf : Etale f], restrictEtale 𝒢 f hf = restrict 𝒢 f)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective.restrict :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (ℱ : Y.Modules) (f : X ⟶ Y)
    [Etale f] [ℱ.IsQuasicoherent],
    IsLocallyProjective ℱ → IsLocallyProjective (restrict ℱ f))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isLocallyProjective_iff_forall_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    IsLocallyProjective ℱ ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
        IsLocallyProjective (restrict ℱ φ))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isLocallyProjective_iff_exists_surjective_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    IsLocallyProjective ℱ ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ),
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          IsLocallyProjective (restrictEtale ℱ φ hφ))
