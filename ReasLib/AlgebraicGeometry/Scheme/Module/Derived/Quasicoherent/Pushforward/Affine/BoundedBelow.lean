/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Coextension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open DerivedCategory.Plus
open DerivedCategory.Plus.CohomologyIn
open AlgebraicGeometry
open RingedSpace.Hom RingedSpace.ModuleDerived
open RingedSpace.Hom.PushforwardStructure
open SheafOfModules.RingedSite.DerivedCoextension
open RingedSpace.ModuleDerived.KFlat
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}}

/-- The bounded-below derived category of modules with quasi-coherent cohomology over the
pushed-forward structure sheaf `f_*𝒪_Y`. -/
abbrev PushforwardQCohPlus (f : Y ⟶ X) :=
  CohomologyIn
    (RingedSpace.quasiCoherentModuleProperty
      (target f.toShHom))

/-- Derived coextension from bounded-below quasi-coherent complexes on `X`, viewed in the
ambient derived category of modules over `f_*𝒪_Y`. -/
noncomputable abbrev derivedCoextensionAmbient (f : Y ⟶ X) :
    Plus X ⥤ RingedSpace.ModuleDerived
      (target f.toShHom) :=
  CohomologyIn.ambient
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
    functor.{u, u}
      (commRingSheafPushforwardMap f.toShHom)

/-- Pseudo-coherence and finiteness make derived coextension preserve bounded-below
objects. -/
theorem derivedCoextensionAmbient_boundedBelow (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] :
    ∀ K : Plus X,
      (t.plus : ObjectProperty
        (RingedSpace.ModuleDerived
          (target f.toShHom)))
        ((derivedCoextensionAmbient f).obj K) := sorry

/-- The bounded-below lift of derived coextension along `𝒪_X ⟶ f_*𝒪_Y`. -/
noncomputable def derivedCoextensionToPlus (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] :
    Plus X ⥤ DerivedCategory.Plus
      (target f.toShHom).Modules :=
  (t.plus : ObjectProperty
      (RingedSpace.ModuleDerived
        (target f.toShHom))).lift
    (derivedCoextensionAmbient f) (derivedCoextensionAmbient_boundedBelow f)

/-- Derived coextension from a bounded-below quasi-coherent complex has quasi-coherent
cohomology over `f_*𝒪_Y`. -/
theorem derivedCoextensionToPlus_quasicoherent (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] :
    ∀ K : Plus X,
      cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty
          (target f.toShHom))
        ((derivedCoextensionToPlus f).obj K) := sorry

/-- The bounded-below finite pseudo-coherent internal-Hom/coextension functor. -/
noncomputable def derivedInternalHomPlus (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] : Plus X ⥤ PushforwardQCohPlus f :=
  (cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty
        (target f.toShHom))).lift
    (derivedCoextensionToPlus f) (derivedCoextensionToPlus_quasicoherent f)

/-- The underlying `𝒪_X`-linear functor of the bounded internal-Hom construction is derived
internal Hom from `f_*𝒪_Y`. -/
theorem derivedInternalHomPlus_restriction_isomorphic
    (f : Y ⟶ X) [IsFinite f] [PseudoCoherent f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) :
    IsIsomorphic
      (derivedInternalHomPlus f ⋙
        CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty
            (target f.toShHom)) ⋙
        restriction.{u, u}
          (commRingSheafPushforwardMap f.toShHom))
      (CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
        MonoidalClosed.ihomOf H (pushforwardStructureSheaf f).obj) := sorry

/-- The chosen right adjoint to derived pushforward, viewed as an ambient functor on
bounded-below objects. -/
noncomputable abbrev rightAdjointAmbient
    (a : DerivedQCoh X ⥤ DerivedQCoh Y) :
    Plus X ⥤ RingedSpace.ModuleDerived Y.toRingedSpace :=
  toUnbounded
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙ a ⋙
    (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).ι

/-- A finite morphism over a quasi-compact, quasi-separated target gives a bounded-below
ambient right-adjoint image. -/
theorem rightAdjointAmbient_boundedBelow (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] [CompactSpace X] [QuasiSeparatedSpace X]
    (a : DerivedQCoh X ⥤ DerivedQCoh Y)
    (adj : pushforwardCohomologyIn f ⊣ a) :
    ∀ K : Plus X,
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace))
        ((rightAdjointAmbient a).obj K) := sorry

/-- The lift of a chosen right adjoint to the bounded-below ambient derived category. -/
noncomputable def rightAdjointToPlus (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] [CompactSpace X] [QuasiSeparatedSpace X]
    (a : DerivedQCoh X ⥤ DerivedQCoh Y)
    (adj : pushforwardCohomologyIn f ⊣ a) :
    Plus X ⥤ DerivedCategory.Plus Y.toRingedSpace.Modules :=
  (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)).lift
    (rightAdjointAmbient a) (rightAdjointAmbient_boundedBelow f a adj)

/-- The bounded-below lift of a chosen right adjoint retains quasi-coherent cohomology. -/
theorem rightAdjointToPlus_quasicoherent (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] [CompactSpace X] [QuasiSeparatedSpace X]
    (a : DerivedQCoh X ⥤ DerivedQCoh Y)
    (adj : pushforwardCohomologyIn f ⊣ a) :
    ∀ K : Plus X,
      DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)
        ((rightAdjointToPlus f a adj).obj K) := sorry

/-- The bounded-below restriction of a chosen right adjoint to derived pushforward. -/
noncomputable def rightAdjointPlus (f : Y ⟶ X)
    [IsFinite f] [PseudoCoherent f] [CompactSpace X] [QuasiSeparatedSpace X]
    (a : DerivedQCoh X ⥤ DerivedQCoh Y)
    (adj : pushforwardCohomologyIn f ⊣ a) : Plus X ⥤ Plus Y :=
  (DerivedCategory.Plus.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).lift
    (rightAdjointToPlus f a adj) (rightAdjointToPlus_quasicoherent f a adj)

/-- The ambient affine pushforward to the pushed-forward structure sheaf on bounded-below
objects. -/
noncomputable abbrev affinePushforwardAmbient (f : Y ⟶ X) [IsFinite f] :
    Plus Y ⥤ RingedSpace.ModuleDerived
      (target f.toShHom) :=
  toUnbounded
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
    affinePushforwardToPushforwardStructure f ⋙
    (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty
        (target f.toShHom))).ι

/-- Affine pushforward to the pushed-forward structure sheaf preserves the bounded-below
condition. -/
theorem affinePushforwardAmbient_boundedBelow (f : Y ⟶ X) [IsFinite f] :
    ∀ K : Plus Y,
      (t.plus : ObjectProperty
        (RingedSpace.ModuleDerived
          (target f.toShHom)))
        ((affinePushforwardAmbient f).obj K) := sorry

/-- The lift of affine pushforward to the bounded-below ambient derived category. -/
noncomputable def affinePushforwardToPlus (f : Y ⟶ X) [IsFinite f] :
    Plus Y ⥤ DerivedCategory.Plus
      (target f.toShHom).Modules :=
  (t.plus : ObjectProperty
      (RingedSpace.ModuleDerived
        (target f.toShHom))).lift
    (affinePushforwardAmbient f) (affinePushforwardAmbient_boundedBelow f)

/-- The bounded-below lift of affine pushforward retains quasi-coherent cohomology. -/
theorem affinePushforwardToPlus_quasicoherent (f : Y ⟶ X) [IsFinite f] :
    ∀ K : Plus Y,
      cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty
          (target f.toShHom))
        ((affinePushforwardToPlus f).obj K) := sorry

/-- The bounded-below restriction of the canonical affine pushforward equivalence. -/
noncomputable def affinePushforwardToPushforwardStructurePlus (f : Y ⟶ X)
    [IsFinite f] : Plus Y ⥤ PushforwardQCohPlus f :=
  (cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty
        (target f.toShHom))).lift
    (affinePushforwardToPlus f) (affinePushforwardToPlus_quasicoherent f)

/-- The bounded-below affine pushforward is an equivalence. -/
noncomputable instance affinePushforwardToPushforwardStructurePlus.isEquivalence
    (f : Y ⟶ X) [IsFinite f] :
    Functor.IsEquivalence (affinePushforwardToPushforwardStructurePlus f) := sorry

/-- The bounded-below affine equivalence agrees with the affine equivalence after passing to
unbounded derived categories. -/
theorem affinePushforwardToPushforwardStructurePlus_comp_toUnbounded_isomorphic
    (f : Y ⟶ X) [IsFinite f] :
    IsIsomorphic
      (affinePushforwardToPushforwardStructurePlus f ⋙
        toUnbounded
          (RingedSpace.quasiCoherentModuleProperty
            (target f.toShHom)))
      (toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) ⋙
        affinePushforwardToPushforwardStructure f) := sorry

/-- The bounded-below right adjoint followed by the affine equivalence is the bounded
internal-Hom functor. -/
theorem rightAdjointPlus_comp_affinePushforwardPlus_isomorphic
    (f : Y ⟶ X) [IsFinite f] [PseudoCoherent f]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (a : DerivedQCoh X ⥤ DerivedQCoh Y)
    (adj : pushforwardCohomologyIn f ⊣ a) :
    IsIsomorphic
      (rightAdjointPlus f a adj ⋙ affinePushforwardToPushforwardStructurePlus f)
      (derivedInternalHomPlus f) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
