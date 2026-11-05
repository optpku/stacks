/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport.SpacePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

/-!
# Space-level Hilbert–Quot comparison for a finite-presentation morphism

The common point data and pullback for arbitrary test algebraic spaces live in
`Hilbert.Functor`. This module compares those points with quotients of the
structure sheaf; here the ambient morphism is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (spaceFiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace SpacePoint

/-- The pushforward `ι_* 𝒪_Z` in the encoding of `Hom.idealSheafMap`. -/
def toQuotSpacePointModule {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) : (Limits.pullback f h).Modules :=
  (SheafOfModules.pushforward
      (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap p.subspace.ι))).obj
    (SheafOfModules.unit ((ringPushforward p.subspace.ι).obj
      (structureSheaf p.subspace.X)))

/-- The quotient map `π^* 𝒪_X ⟶ ι_* 𝒪_Z` obtained by transporting
`Hom.idealSheafMap` along `Modules.structureModulePullbackIso`. -/
def toQuotSpacePointMap {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) :
    Quot.spaceFiberF f (SheafOfModules.unit (structureSheaf X)) h ⟶
      toQuotSpacePointModule p :=
  (Modules.structureModulePullbackIso (pullback.fst f h)).inv ≫
    Hom.idealSheafMap p.subspace.ι

/-- The quotient onto the pushed-forward structure module is an epimorphism with
quasi-coherent finitely presented target, flat over the base and with proper support. -/
theorem toQuotSpacePoint_properties {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) :
    Epi (toQuotSpacePointMap p) ∧ (toQuotSpacePointModule p).IsQuasicoherent ∧
      Modules.flatOver (toQuotSpacePointModule p) (pullback.snd f h) ∧
      (toQuotSpacePointModule p).IsFinitePresentation ∧
      Quot.supportProperOver (pullback.snd f h) (toQuotSpacePointModule p) := sorry

/-- The space-level Quot-point `𝒪_{X_T} ⟶ ι_* 𝒪_Z` associated to a space-level
Hilbert point. -/
def toQuotSpacePoint {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) :
    Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h :=
  Quot.QuotSpacePoint.ofEpi f (SheafOfModules.unit (structureSheaf X)) h
    (toQuotSpacePointModule p) (toQuotSpacePointMap p)
    (toQuotSpacePoint_properties p).1 (toQuotSpacePoint_properties p).2.1
    (toQuotSpacePoint_properties p).2.2.1 (toQuotSpacePoint_properties p).2.2.2.1
    (toQuotSpacePoint_properties p).2.2.2.2

/-- The module of `toQuotSpacePoint p` is `ι_* 𝒪_Z` in the encoding of
`Hom.idealSheafMap`. -/
theorem toQuotSpacePoint_module {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) :
    (toQuotSpacePoint p).point.module = toQuotSpacePointModule p := rfl

/-- The quotient map of `toQuotSpacePoint p` is `Hom.idealSheafMap` transported
along `Modules.structureModulePullbackIso`. -/
theorem toQuotSpacePoint_map {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) :
    (toQuotSpacePoint p).point.map = toQuotSpacePointMap p := rfl

/-- The structure-sheaf quotient `𝒪_{X_T} ⟶ Q` obtained by transporting a
space-level Quot-point of `𝒪_X` along `Modules.structureModulePullbackIso`. -/
def ofQuotSpacePointMap {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    SheafOfModules.unit (structureSheaf (Limits.pullback f h)) ⟶ Q.point.module :=
  (Modules.structureModulePullbackIso (pullback.fst f h)).hom ≫ Q.point.map

/-- The quasi-coherent ideal `I = Ker(𝒪_{X_T} ⟶ Q)` of a space-level Quot-point
of `𝒪_X`. -/
def ofQuotSpacePointKernel {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    IdealSubobject (Limits.pullback f h) :=
  kernelSubobject (ofQuotSpacePointMap Q)

/-- The kernel of a space-level Quot-point of `𝒪_X` is a quasi-coherent ideal
sheaf on `X_T`. -/
theorem ofQuotSpacePointKernel_isQuasiCoherent {T : AlgebraicSpace S}
    {f : X ⟶ B} {h : T ⟶ B} [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    IsQuasiCoherent (ofQuotSpacePointKernel Q) := by
  letI := Q.point.isQuasicoherent
  refine ⟨?_⟩
  show quasiCoherentModuleProperty (Limits.pullback f h) (ofQuotSpacePointKernel Q).toModule
  exact (quasiCoherentModuleProperty (Limits.pullback f h)).prop_of_iso
    (kernelSubobjectIso (ofQuotSpacePointMap Q)).symm
    (inferInstanceAs (kernel (ofQuotSpacePointMap Q)).IsQuasicoherent)

/-- The closed subspace of `X_T` cut out by `Ker(𝒪_{X_T} ⟶ Q)`. -/
def ofQuotSpacePointSubspace {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    ClosedSubspace (Limits.pullback f h) :=
  @ClosedSubspace.ofQuasiCoherentIdeal S (Limits.pullback f h)
    (ofQuotSpacePointKernel Q) (ofQuotSpacePointKernel_isQuasiCoherent Q)

/-- The closed subspace cut out by a proper-support quotient of the structure
module is finitely presented, flat, and proper over the base. -/
theorem ofQuotSpacePointSubspace_properties {T : AlgebraicSpace S}
    {f : X ⟶ B} {h : T ⟶ B} [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    FinitePresentation ((ofQuotSpacePointSubspace Q).ι ≫ pullback.snd f h) ∧
      Flat ((ofQuotSpacePointSubspace Q).ι ≫ pullback.snd f h) ∧
      Proper ((ofQuotSpacePointSubspace Q).ι ≫ pullback.snd f h) := sorry

/-- The space-level Hilbert point cut out by the kernel of a space-level
Quot-point of `𝒪_X`. -/
def ofQuotSpacePoint {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    SpacePoint f h where
  subspace := ofQuotSpacePointSubspace Q
  isFinitePresentation := (ofQuotSpacePointSubspace_properties Q).1
  isFlat := (ofQuotSpacePointSubspace_properties Q).2.1
  isProper := (ofQuotSpacePointSubspace_properties Q).2.2

/-- The closed subspace of `ofQuotSpacePoint Q` is the vanishing locus of
`Ker(𝒪_{X_T} ⟶ Q)`. -/
theorem ofQuotSpacePoint_spec {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    (ofQuotSpacePoint Q).subspace.idealSheaf = ofQuotSpacePointKernel Q :=
  @ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf S (Limits.pullback f h)
    (ofQuotSpacePointKernel Q) (ofQuotSpacePointKernel_isQuasiCoherent Q)

end SpacePoint

end AlgebraicGeometry.AlgebraicSpace.Hilbert
