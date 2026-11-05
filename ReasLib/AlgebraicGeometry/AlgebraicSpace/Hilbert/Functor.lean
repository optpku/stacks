/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.SpacePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# The Grothendieck Hilbert functor on algebraic spaces

This module constructs the contravariant Hilbert functor of an arbitrary
morphism of algebraic spaces. A test scheme `T` over `B` is sent to the set of
closed subspaces `Z ⊂ X_T` for which `Z ⟶ T` is of finite presentation, flat,
and proper, identified when they have the same ideal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (fiber fiberMap spaceFiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A closed subspace `Z ⊂ X_T` whose structure morphism `Z ⟶ T` is of finite
presentation, flat, and proper, for an algebraic space `T` over `S`. -/
structure SpacePoint {T : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B) where
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
def ofι {T : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
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
    (p : SpacePoint f h) : p.subspace.X ⟶ T :=
  p.subspace.ι ≫ pullback.snd f h

/-- A space-level Hilbert point is a closed subspace `Z ⊂ X_T` with `Z ⟶ T` of
finite presentation, flat, and proper. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    (p : SpacePoint f h) :
    IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
      Flat p.structureMap ∧ Proper p.structureMap :=
  ⟨p.subspace.isClosedImmersion, p.isFinitePresentation, p.isFlat, p.isProper⟩

/-- Two space-level Hilbert points are identified when they have the same
ideal sheaf. -/
def Rel {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    (p q : SpacePoint f h) : Prop :=
  p.subspace.idealSheaf = q.subspace.idealSheaf

/-- Identification of space-level Hilbert points is equality of ideal sheaves. -/
theorem Rel_iff_idealSheaf {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    (p q : SpacePoint f h) :
    Rel p q ↔ p.subspace.idealSheaf = q.subspace.idealSheaf := Iff.rfl

/-- Ideal-sheaf equality is an equivalence relation on space-level Hilbert
points. -/
theorem rel_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B)
    (h : T ⟶ B) :
    Equivalence (fun p q : SpacePoint f h ↦ Rel p q) where
  refl _ := rfl
  symm hpq := hpq.symm
  trans hpq hqr := hpq.trans hqr

/-- The structure morphism of the inverse image of a Hilbert subspace is
finitely presented, flat, and proper over the new base. -/
theorem pullback_properties {T T' : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    (p : SpacePoint f h) (a : T' ⟶ T) :
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
    (p : SpacePoint f h) (a : T' ⟶ T) :
    SpacePoint f (a ≫ h) where
  subspace := p.subspace.inverseImageSubspace (spaceFiberMap f h a)
  isFinitePresentation := (pullback_properties p a).1
  isFlat := (pullback_properties p a).2.1
  isProper := (pullback_properties p a).2.2

/-- The closed subspace of a pulled-back space-level Hilbert point is the
inverse image along `spaceFiberMap`. -/
theorem pullback_subspace {T T' : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    (p : SpacePoint f h) (a : T' ⟶ T) :
    (p.pullback a).subspace = p.subspace.inverseImageSubspace (spaceFiberMap f h a) := rfl


/-- Pull back along a morphism over `B`, retaining the specified structure map.
Only the supplied commutativity equality is used to reindex the common pullback. -/
def pullbackOver {T T' : AlgebraicSpace S} {f : X ⟶ B}
    {h : T ⟶ B} {h' : T' ⟶ B} (p : SpacePoint f h)
    (a : T' ⟶ T) (w : a ≫ h = h') : SpacePoint f h' :=
  w ▸ p.pullback a

/-- Reindexing along the structure-map equality retains the canonical inverse
image along the map of fibre products. -/
theorem pullbackOver_subspace {T T' : AlgebraicSpace S} {f : X ⟶ B}
    {h : T ⟶ B} {h' : T' ⟶ B} (p : SpacePoint f h)
    (a : T' ⟶ T) (w : a ≫ h = h') :
    (p.pullbackOver a w).subspace =
      p.subspace.inverseImageSubspace (pullback.map f h' f h (𝟙 X) a (𝟙 B)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id h').trans w.symm)) := by
  subst h'
  rfl

/-- The structure morphism after base change over `B` retains the three
Hilbert-point properties, without a condition on the ambient morphism `f`. -/
theorem pullbackOver_properties {T T' : AlgebraicSpace S} {f : X ⟶ B}
    {h : T ⟶ B} {h' : T' ⟶ B} (p : SpacePoint f h)
    (a : T' ⟶ T) (w : a ≫ h = h') :
    FinitePresentation
        ((p.subspace.inverseImageSubspace (pullback.map f h' f h (𝟙 X) a (𝟙 B)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id h').trans w.symm))).ι ≫ pullback.snd f h') ∧
      Flat ((p.subspace.inverseImageSubspace (pullback.map f h' f h (𝟙 X) a (𝟙 B)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id h').trans w.symm))).ι ≫ pullback.snd f h') ∧
      Proper ((p.subspace.inverseImageSubspace (pullback.map f h' f h (𝟙 X) a (𝟙 B)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id h').trans w.symm))).ι ≫ pullback.snd f h') := by
  subst h'
  exact pullback_properties p a

set_option maxHeartbeats 1000000 in
/-- Base change preserves equality of the ideal sheaves of Hilbert points. -/
theorem rel_pullbackOver {T T' : AlgebraicSpace S} {f : X ⟶ B}
    {h : T ⟶ B} {h' : T' ⟶ B} (p q : SpacePoint f h) (hpq : Rel p q)
    (a : T' ⟶ T) (w : a ≫ h = h') :
    Rel (p.pullbackOver a w) (q.pullbackOver a w) := by
  subst h'
  change (p.subspace.inverseImageSubspace (spaceFiberMap f h a)).idealSheaf =
    (q.subspace.inverseImageSubspace (spaceFiberMap f h a)).idealSheaf
  rw [ClosedSubspace.inverseImage_idealSheaf, ClosedSubspace.inverseImage_idealSheaf]
  exact congrArg (fun I : IdealSubobject (Limits.pullback f h) ↦
    I.pullback (spaceFiberMap f h a)) hpq

end SpacePoint

/-- The setoid of space-level Hilbert points modulo equal ideal sheaves. -/
def spaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B)
    (h : T ⟶ B) : Setoid (SpacePoint f h) where
  r := SpacePoint.Rel
  iseqv := SpacePoint.rel_isEquivalence f h

/-- Pullback preserves ideal-sheaf identification of space-level Hilbert
points. -/
theorem spaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B)
    (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (p q : SpacePoint f h),
      (spaceSetoid f h).r p q →
        (spaceSetoid f (a ≫ h)).r (p.pullback a) (q.pullback a) := by
  intro p q hpq
  exact SpacePoint.rel_pullbackOver p q hpq a rfl

/-- A pair `(h, Z)` consisting of a morphism `h : T ⟶ B` and an ideal-sheaf
identified closed subspace of `X_T` that is of finite presentation, flat, and
proper over `T`. -/
structure SpacePair (f : X ⟶ B) (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The ideal-sheaf identified closed subspace class of `X_T`. -/
  subspace : _root_.Quotient (spaceSetoid f hom)

namespace SpacePair

/-- Package a space-level Hilbert point over `h : T ⟶ B` as the pair
`(h, [Z])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {h : T ⟶ B}
    (p : SpacePoint f h) : SpacePair f T where
  hom := h
  subspace := _root_.Quotient.mk (spaceSetoid f h) p

/-- Pull back a space-level Hilbert pair `(h, Z)` along `a : T' ⟶ T`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B}
    (P : SpacePair f T) (a : T' ⟶ T) : SpacePair f T' where
  hom := a ≫ P.hom
  subspace :=
    _root_.Quotient.map (fun p : SpacePoint f P.hom ↦ p.pullback a)
      (spaceSetoid_rel_pullback f P.hom a) P.subspace

/-- The morphism of a pulled-back space-level Hilbert pair is the composite
`a ≫ P.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B}
    (P : SpacePair f T) (a : T' ⟶ T) :
    (P.pullback a).hom = a ≫ P.hom := rfl

/-- Every Hilbert pair has a representative closed subspace with finitely
presented, flat, proper structure morphism and the specified quotient class. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B}
    (P : SpacePair f T) :
    ∃ p : SpacePoint f P.hom,
      _root_.Quotient.mk (spaceSetoid f P.hom) p = P.subspace ∧
        IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
        Flat p.structureMap ∧ Proper p.structureMap := by
  obtain ⟨p, hp⟩ := _root_.Quotient.exists_rep P.subspace
  exact ⟨p, hp, p.spec⟩

end SpacePair


/-- Scheme-level facade for the common Hilbert-point data.
This record retains the original constructor and projections over `Quot.fiber`;
its operations are obtained from `SpacePoint` through the inverse repackagings. -/
structure Point (f : X ⟶ B) (σ : SchemeOver B) where
  /-- The closed subspace of the base change `X_T`. -/
  subspace : ClosedSubspace (fiber f σ)
  /-- The structure morphism `Z ⟶ T` is of finite presentation. -/
  isFinitePresentation : FinitePresentation (subspace.ι ≫ pullback.snd f σ.hom)
  /-- The structure morphism `Z ⟶ T` is flat. -/
  isFlat : Flat (subspace.ι ≫ pullback.snd f σ.hom)
  /-- The structure morphism `Z ⟶ T` is proper. -/
  isProper : Proper (subspace.ι ≫ pullback.snd f σ.hom)


/-- View a scheme-level Hilbert point as common data along `σ.hom`. -/
def Point.toSpacePoint {f : X ⟶ B} {σ : SchemeOver B}
    (p : Point f σ) : SpacePoint f σ.hom where
  subspace := p.subspace
  isFinitePresentation := p.isFinitePresentation
  isFlat := p.isFlat
  isProper := p.isProper

/-- Repackage common Hilbert-point data over a scheme, preserving its subspace. -/
def Point.ofSpacePoint {f : X ⟶ B} {σ : SchemeOver B}
    (p : SpacePoint f σ.hom) : Point f σ where
  subspace := p.subspace
  isFinitePresentation := p.isFinitePresentation
  isFlat := p.isFlat
  isProper := p.isProper

/-- The scheme and space views retain exactly the same closed subspace. -/
theorem Point.toSpacePoint_subspace {f : X ⟶ B} {σ : SchemeOver B}
    (p : Point f σ) : p.toSpacePoint.subspace = p.subspace := rfl

/-- Repackaging a scheme point through the common data is the identity. -/
theorem Point.ofSpacePoint_toSpacePoint {f : X ⟶ B} {σ : SchemeOver B}
    (p : Point f σ) : ofSpacePoint p.toSpacePoint = p := rfl

/-- Repackaging common data through the scheme wrapper is the identity. -/
theorem Point.toSpacePoint_ofSpacePoint {f : X ⟶ B} {σ : SchemeOver B}
    (p : SpacePoint f σ.hom) : (Point.ofSpacePoint p).toSpacePoint = p := rfl

namespace Point

/-- Construct a Hilbert point from a closed immersion `Z ⟶ X_T` whose composite
to `T` is of finite presentation, flat, and proper. -/
def ofι (f : X ⟶ B) (σ : SchemeOver B)
    {Z : AlgebraicSpace S} (i : Z ⟶ fiber f σ) [IsClosedImmersion i]
    (isFinitePresentation : FinitePresentation (i ≫ pullback.snd f σ.hom))
    (isFlat : Flat (i ≫ pullback.snd f σ.hom))
    (isProper : Proper (i ≫ pullback.snd f σ.hom)) : Point f σ where
  subspace := ClosedSubspace.ofι i
  isFinitePresentation := isFinitePresentation
  isFlat := isFlat
  isProper := isProper

/-- The structure morphism `Z ⟶ T` of a Hilbert point. -/
def structureMap {f : X ⟶ B} {σ : SchemeOver B}
    (p : Point f σ) : p.subspace.X ⟶ (ofOverFunctor S).obj σ.left :=
  p.subspace.ι ≫ pullback.snd f σ.hom

/-- A Hilbert point is a closed subspace `Z ⊂ X_T` with `Z ⟶ T` of finite
presentation, flat, and proper. -/
theorem spec {f : X ⟶ B} {σ : SchemeOver B}
    (p : Point f σ) :
    IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
      Flat p.structureMap ∧ Proper p.structureMap := p.toSpacePoint.spec

/-- The structure morphism of the inverse image of a Hilbert point is of finite
presentation, flat, and proper. -/
theorem pullback_properties {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) :
    FinitePresentation
        ((p.subspace.inverseImageSubspace (fiberMap f h)).ι ≫ pullback.snd f τ.hom) ∧
      Flat ((p.subspace.inverseImageSubspace (fiberMap f h)).ι ≫ pullback.snd f τ.hom) ∧
      Proper ((p.subspace.inverseImageSubspace (fiberMap f h)).ι ≫ pullback.snd f τ.hom) :=
  SpacePoint.pullbackOver_properties p.toSpacePoint _ (CostructuredArrow.w h)

/-- Pull back a Hilbert point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) : Point f τ :=
  ofSpacePoint (p.toSpacePoint.pullbackOver ((ofOverFunctor S).map h.left)
    (CostructuredArrow.w h))

/-- The closed subspace of a pulled-back Hilbert point is the inverse image
along `fiberMap`. -/
theorem pullback_subspace {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) :
    (p.pullback h).subspace = p.subspace.inverseImageSubspace (fiberMap f h) :=
  SpacePoint.pullbackOver_subspace p.toSpacePoint _ (CostructuredArrow.w h)

/-- Scheme pullback is the common pullback over `B`, including its structure map. -/
theorem toSpacePoint_pullback {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) :
    (p.pullback h).toSpacePoint =
      p.toSpacePoint.pullbackOver ((ofOverFunctor S).map h.left)
        (CostructuredArrow.w h) := rfl

end Point

/-- Two Hilbert points are identified when they have the same ideal sheaf. -/
def Rel {f : X ⟶ B} {σ : SchemeOver B}
    (p q : Point f σ) : Prop :=
  SpacePoint.Rel p.toSpacePoint q.toSpacePoint

/-- Identification of Hilbert points is equality of ideal sheaves. -/
theorem Rel_iff_idealSheaf {f : X ⟶ B} {σ : SchemeOver B}
    (p q : Point f σ) :
    Rel p q ↔ p.subspace.idealSheaf = q.subspace.idealSheaf := Iff.rfl

/-- Identification of Hilbert points is equivalent to an isomorphism of closed
subspaces over `X_T`. -/
theorem Rel_iff_overIso {f : X ⟶ B} {σ : SchemeOver B}
    (p q : Point f σ) :
    Rel p q ↔ Nonempty (Over.mk p.subspace.ι ≅ Over.mk q.subspace.ι) :=
  sorry

/-- Ideal-sheaf equality is an equivalence relation on Hilbert points. -/
theorem rel_isEquivalence (f : X ⟶ B) (σ : SchemeOver B) :
    Equivalence (fun p q : Point f σ ↦ Rel p q) where
  refl _ := rfl
  symm hpq := hpq.symm
  trans hpq hqr := hpq.trans hqr

/-- The setoid of Hilbert points modulo equal ideal sheaves. -/
def setoid (f : X ⟶ B) (σ : SchemeOver B) :
    Setoid (Point f σ) where
  r := Rel
  iseqv := rel_isEquivalence f σ

set_option maxHeartbeats 1000000 in
/-- Pullback preserves ideal-sheaf identification of Hilbert points. -/
theorem setoid_rel_pullback (f : X ⟶ B)
    {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    ∀ (p q : Point f σ),
      (setoid f σ).r p q → (setoid f τ).r (p.pullback h) (q.pullback h) := by
  intro p q hpq
  exact SpacePoint.rel_pullbackOver (h' := τ.hom) p.toSpacePoint q.toSpacePoint hpq
    ((ofOverFunctor S).map h.left) (CostructuredArrow.w h)

/-- Pullback along the identity induces the identity on identified Hilbert
classes. -/
theorem hilbert_map_id (f : X ⟶ B)
    (σ : (SchemeOver B)ᵒᵖ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback (𝟙 σ).unop)
        (setoid_rel_pullback f (𝟙 σ).unop)) =
      𝟙 (_root_.Quotient (setoid f σ.unop)) :=
  sorry

/-- Pullback along a composite induces the composite of the pullback maps on
Hilbert classes. -/
theorem hilbert_map_comp (f : X ⟶ B)
    {σ τ ρ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback (h ≫ k).unop)
        (setoid_rel_pullback f (h ≫ k).unop)) =
      TypeCat.ofHom
          (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback h.unop)
            (setoid_rel_pullback f h.unop)) ≫
        TypeCat.ofHom
          (_root_.Quotient.map (fun p : Point f τ.unop ↦ p.pullback k.unop)
            (setoid_rel_pullback f k.unop)) :=
  sorry

/-- The Grothendieck Hilbert functor `Hilb_{X/B}` of closed subspaces of
`X_T` that are of finite presentation, flat, and proper over the test scheme,
identified by equal ideal sheaves. -/
def functor (f : X ⟶ B) :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (setoid f σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback h.unop)
        (setoid_rel_pullback f h.unop))
  map_id := hilbert_map_id f
  map_comp := hilbert_map_comp f

/-- The value of the Hilbert functor is the quotient by equality of ideal sheaves. -/
theorem functor_obj (f : X ⟶ B) (σ : SchemeOver B) :
    (functor f).obj (op σ) = _root_.Quotient (setoid f σ) := rfl

/-- The Hilbert functor acts by inverse image of closed subspaces. -/
theorem functor_map (f : X ⟶ B)
    {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (functor f).map h =
      TypeCat.ofHom
        (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback h.unop)
          (setoid_rel_pullback f h.unop)) := rfl

/-- The Hilbert functor of a finite-presentation morphism. -/
def hilbert (f : X ⟶ B) [FinitePresentation f] :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) := functor f

/-- The value of the Hilbert functor is the setoid quotient of Hilbert points by
equal ideal sheaves. -/
theorem hilbert_obj (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    (hilbert f).obj (op σ) = _root_.Quotient (setoid f σ) :=
  sorry

/-- The Hilbert functor acts on a morphism by pullback of Hilbert points. -/
theorem hilbert_map (f : X ⟶ B) [FinitePresentation f]
    {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (hilbert f).map h =
      TypeCat.ofHom
        (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback h.unop)
          (setoid_rel_pullback f h.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
