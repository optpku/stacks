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
# Space-level Hilbert points of a finite-presentation morphism

This module extends the scheme-level Hilbert points of `Hilb_{X/B}` to an
algebraic space `T` over `S`, via a morphism `h : T ⟶ B` and an ideal-sheaf
identified closed subspace `Z ⊂ X ×_{B,h} T` whose structure morphism
`Z ⟶ T` is of finite presentation, flat, and proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (spaceFiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A closed subspace `Z ⊂ X_T` whose structure morphism `Z ⟶ T` is of finite
presentation, flat, and proper, for an algebraic space `T` over `S`. -/
structure SpacePoint {T : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    [FinitePresentation f] where
  /-- The closed subspace of the base change `X_T = X ×_{B,h} T`. -/
  subspace : ClosedSubspace (pullback f h)
  /-- The structure morphism `Z ⟶ T` is of finite presentation. -/
  isFinitePresentation : FinitePresentation (subspace.ι ≫ pullback.snd f h)
  /-- The structure morphism `Z ⟶ T` is flat. -/
  isFlat : Flat (subspace.ι ≫ pullback.snd f h)
  /-- The structure morphism `Z ⟶ T` is proper. -/
  isProper : Proper (subspace.ι ≫ pullback.snd f h)

namespace SpacePoint

/-- Construct a space-level Hilbert point from a closed immersion `Z ⟶ X_T`
whose composite to `T` is of finite presentation, flat, and proper. -/
def ofι {T : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B) [FinitePresentation f]
    {Z : AlgebraicSpace S} (i : Z ⟶ pullback f h) [IsClosedImmersion i]
    (isFinitePresentation : FinitePresentation (i ≫ pullback.snd f h))
    (isFlat : Flat (i ≫ pullback.snd f h))
    (isProper : Proper (i ≫ pullback.snd f h)) : SpacePoint f h where
  subspace := ClosedSubspace.ofι i
  isFinitePresentation := isFinitePresentation
  isFlat := isFlat
  isProper := isProper

/-- The structure morphism `Z ⟶ T` of a space-level Hilbert point. -/
def structureMap {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) : p.subspace.X ⟶ T :=
  p.subspace.ι ≫ pullback.snd f h

/-- A space-level Hilbert point is a closed subspace `Z ⊂ X_T` with `Z ⟶ T` of
finite presentation, flat, and proper. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) :
    IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
      Flat p.structureMap ∧ Proper p.structureMap :=
  ⟨p.subspace.isClosedImmersion, p.isFinitePresentation, p.isFlat, p.isProper⟩

/-- Two space-level Hilbert points are identified when they have the same
ideal sheaf. -/
def Rel {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B} [FinitePresentation f]
    (p q : SpacePoint f h) : Prop :=
  p.subspace.idealSheaf = q.subspace.idealSheaf

/-- Identification of space-level Hilbert points is equality of ideal sheaves. -/
theorem Rel_iff_idealSheaf {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p q : SpacePoint f h) :
    Rel p q ↔ p.subspace.idealSheaf = q.subspace.idealSheaf := Iff.rfl

/-- Ideal-sheaf equality is an equivalence relation on space-level Hilbert
points. -/
theorem rel_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (h : T ⟶ B) :
    Equivalence (fun p q : SpacePoint f h ↦ Rel p q) where
  refl _ := rfl
  symm hpq := hpq.symm
  trans hpq hqr := hpq.trans hqr

/-- The pushforward `ι_* 𝒪_Z` in the encoding of `Hom.idealSheafMap`. -/
def toQuotSpacePointModule {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) : (pullback f h).Modules :=
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
    SheafOfModules.unit (structureSheaf (pullback f h)) ⟶ Q.point.module :=
  (Modules.structureModulePullbackIso (pullback.fst f h)).hom ≫ Q.point.map

/-- The quasi-coherent ideal `I = Ker(𝒪_{X_T} ⟶ Q)` of a space-level Quot-point
of `𝒪_X`. -/
def ofQuotSpacePointKernel {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    IdealSubobject (pullback f h) :=
  kernelSubobject (ofQuotSpacePointMap Q)

/-- The kernel of a space-level Quot-point of `𝒪_X` is a quasi-coherent ideal
sheaf on `X_T`. -/
theorem ofQuotSpacePointKernel_isQuasiCoherent {T : AlgebraicSpace S}
    {f : X ⟶ B} {h : T ⟶ B} [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    IsQuasiCoherent (ofQuotSpacePointKernel Q) := by
  letI := Q.point.isQuasicoherent
  refine ⟨?_⟩
  show quasiCoherentModuleProperty (pullback f h) (ofQuotSpacePointKernel Q).toModule
  exact (quasiCoherentModuleProperty (pullback f h)).prop_of_iso
    (kernelSubobjectIso (ofQuotSpacePointMap Q)).symm
    (inferInstanceAs (kernel (ofQuotSpacePointMap Q)).IsQuasicoherent)

/-- The closed subspace of `X_T` cut out by `Ker(𝒪_{X_T} ⟶ Q)`. -/
def ofQuotSpacePointSubspace {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f]
    (Q : Quot.QuotSpacePoint f (SheafOfModules.unit (structureSheaf X)) h) :
    ClosedSubspace (pullback f h) :=
  @ClosedSubspace.ofQuasiCoherentIdeal S (pullback f h)
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
  @ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf S (pullback f h)
    (ofQuotSpacePointKernel Q) (ofQuotSpacePointKernel_isQuasiCoherent Q)

/-- The structure morphism of the inverse image of a Hilbert subspace is
finitely presented, flat, and proper over the new base. -/
theorem pullback_properties {T T' : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) (a : T' ⟶ T) :
    FinitePresentation
        ((p.subspace.inverseImageSubspace (spaceFiberMap f h a)).ι ≫
          pullback.snd f (a ≫ h)) ∧
      Flat ((p.subspace.inverseImageSubspace (spaceFiberMap f h a)).ι ≫
        pullback.snd f (a ≫ h)) ∧
      Proper ((p.subspace.inverseImageSubspace (spaceFiberMap f h a)).ι ≫
        pullback.snd f (a ≫ h)) := by
  letI := p.subspace.isClosedImmersion
  have baseSquare : IsPullback (spaceFiberMap f h a) (pullback.snd f (a ≫ h))
      (pullback.snd f h) a := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback f h)
    · show IsPullback (spaceFiberMap f h a ≫ pullback.fst f h)
        (pullback.snd f (a ≫ h)) f (a ≫ h)
      simpa [Quot.spaceFiberMap, pullback.map, pullback.lift_fst] using
        (IsPullback.of_hasPullback f (a ≫ h))
    · show spaceFiberMap f h a ≫ pullback.snd f h = pullback.snd f (a ≫ h) ≫ a
      simp [Quot.spaceFiberMap, pullback.map, pullback.lift_snd]
  have square :=
    (inverseImage_isPullback (spaceFiberMap f h a) p.subspace.ι).flip.paste_vert baseSquare
  exact ⟨FinitePresentation.of_isPullback square p.isFinitePresentation,
    Flat.of_isPullback square p.isFlat, Proper.of_isPullback square p.isProper⟩

/-- Pull back a space-level Hilbert point along a morphism of algebraic spaces. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) (a : T' ⟶ T) :
    SpacePoint f (a ≫ h) where
  subspace := p.subspace.inverseImageSubspace (spaceFiberMap f h a)
  isFinitePresentation := (pullback_properties p a).1
  isFlat := (pullback_properties p a).2.1
  isProper := (pullback_properties p a).2.2

/-- The closed subspace of a pulled-back space-level Hilbert point is the
inverse image along `spaceFiberMap`. -/
theorem pullback_subspace {T T' : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    [FinitePresentation f] (p : SpacePoint f h) (a : T' ⟶ T) :
    (p.pullback a).subspace = p.subspace.inverseImageSubspace (spaceFiberMap f h a) := rfl

end SpacePoint

/-- View a scheme-level Hilbert point as a space-level Hilbert point along
`σ.hom`. -/
def Point.toSpacePoint {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) : SpacePoint f σ.hom where
  subspace := p.subspace
  isFinitePresentation := p.isFinitePresentation
  isFlat := p.isFlat
  isProper := p.isProper

/-- The closed subspace of `Point.toSpacePoint p` is the underlying closed
subspace of `p`. -/
theorem Point.toSpacePoint_subspace {f : X ⟶ B} {σ : SchemeOver B}
    [FinitePresentation f] (p : Point f σ) :
    (p.toSpacePoint).subspace = p.subspace := rfl

/-- The setoid of space-level Hilbert points modulo equal ideal sheaves. -/
def spaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (h : T ⟶ B) : Setoid (SpacePoint f h) where
  r := SpacePoint.Rel
  iseqv := SpacePoint.rel_isEquivalence f h

/-- Pullback preserves ideal-sheaf identification of space-level Hilbert
points. -/
theorem spaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (p q : SpacePoint f h),
      (spaceSetoid f h).r p q →
        (spaceSetoid f (a ≫ h)).r (p.pullback a) (q.pullback a) := by
  intro p q hpq
  change (p.subspace.inverseImageSubspace (spaceFiberMap f h a)).idealSheaf =
    (q.subspace.inverseImageSubspace (spaceFiberMap f h a)).idealSheaf
  rw [ClosedSubspace.inverseImage_idealSheaf, ClosedSubspace.inverseImage_idealSheaf]
  exact congrArg (fun I : IdealSubobject (pullback f h) ↦ I.pullback (spaceFiberMap f h a)) hpq

/-- A pair `(h, Z)` consisting of a morphism `h : T ⟶ B` and an ideal-sheaf
identified closed subspace of `X_T` that is of finite presentation, flat, and
proper over `T`. -/
structure SpacePair (f : X ⟶ B) [FinitePresentation f] (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The ideal-sheaf identified closed subspace class of `X_T`. -/
  subspace : _root_.Quotient (spaceSetoid f hom)

namespace SpacePair

/-- Package a space-level Hilbert point over `h : T ⟶ B` as the pair
`(h, [Z])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f] {h : T ⟶ B}
    (p : SpacePoint f h) : SpacePair f T where
  hom := h
  subspace := _root_.Quotient.mk (spaceSetoid f h) p

/-- Pull back a space-level Hilbert pair `(h, Z)` along `a : T' ⟶ T`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f]
    (P : SpacePair f T) (a : T' ⟶ T) : SpacePair f T' where
  hom := a ≫ P.hom
  subspace :=
    _root_.Quotient.map (fun p : SpacePoint f P.hom ↦ p.pullback a)
      (spaceSetoid_rel_pullback f P.hom a) P.subspace

/-- The morphism of a pulled-back space-level Hilbert pair is the composite
`a ≫ P.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B}
    [FinitePresentation f] (P : SpacePair f T) (a : T' ⟶ T) :
    (P.pullback a).hom = a ≫ P.hom := rfl

/-- Every Hilbert pair has a representative closed subspace with finitely
presented, flat, proper structure morphism and the specified quotient class. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f]
    (P : SpacePair f T) :
    ∃ p : SpacePoint f P.hom,
      _root_.Quotient.mk (spaceSetoid f P.hom) p = P.subspace ∧
        IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
        Flat p.structureMap ∧ Proper p.structureMap := by
  obtain ⟨p, hp⟩ := _root_.Quotient.exists_rep P.subspace
  exact ⟨p, hp, p.spec⟩

end SpacePair

end AlgebraicGeometry.AlgebraicSpace.Hilbert
