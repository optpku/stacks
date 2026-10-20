/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
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
open AlgebraicGeometry.AlgebraicSpace.Quot (fiber fiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A closed subspace `Z ⊂ X_T` whose structure morphism `Z ⟶ T` is of finite
presentation, flat, and proper. -/
structure Point (f : X ⟶ B) (σ : SchemeOver B) where
  /-- The closed subspace of the base change `X_T`. -/
  subspace : ClosedSubspace (fiber f σ)
  /-- The structure morphism `Z ⟶ T` is of finite presentation. -/
  isFinitePresentation : FinitePresentation (subspace.ι ≫ pullback.snd f σ.hom)
  /-- The structure morphism `Z ⟶ T` is flat. -/
  isFlat : Flat (subspace.ι ≫ pullback.snd f σ.hom)
  /-- The structure morphism `Z ⟶ T` is proper. -/
  isProper : Proper (subspace.ι ≫ pullback.snd f σ.hom)

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
      Flat p.structureMap ∧ Proper p.structureMap :=
  sorry

/-- The structure morphism of the inverse image of a Hilbert point is of finite
presentation, flat, and proper. -/
theorem pullback_properties {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) :
    FinitePresentation
        ((p.subspace.inverseImageSubspace (fiberMap f h)).ι ≫ pullback.snd f τ.hom) ∧
      Flat ((p.subspace.inverseImageSubspace (fiberMap f h)).ι ≫ pullback.snd f τ.hom) ∧
      Proper ((p.subspace.inverseImageSubspace (fiberMap f h)).ι ≫ pullback.snd f τ.hom) :=
  sorry

/-- Pull back a Hilbert point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) : Point f τ where
  subspace := p.subspace.inverseImageSubspace (fiberMap f h)
  isFinitePresentation := (pullback_properties p h).1
  isFlat := (pullback_properties p h).2.1
  isProper := (pullback_properties p h).2.2

/-- The closed subspace of a pulled-back Hilbert point is the inverse image
along `fiberMap`. -/
theorem pullback_subspace {f : X ⟶ B} {σ τ : SchemeOver B}
    (p : Point f σ) (h : τ ⟶ σ) :
    (p.pullback h).subspace = p.subspace.inverseImageSubspace (fiberMap f h) :=
  sorry

end Point

/-- Two Hilbert points are identified when they have the same ideal sheaf. -/
def Rel {f : X ⟶ B} {σ : SchemeOver B}
    (p q : Point f σ) : Prop :=
  p.subspace.idealSheaf = q.subspace.idealSheaf

/-- Identification of Hilbert points is equality of ideal sheaves. -/
theorem Rel_iff_idealSheaf {f : X ⟶ B} {σ : SchemeOver B}
    (p q : Point f σ) :
    Rel p q ↔ p.subspace.idealSheaf = q.subspace.idealSheaf :=
  sorry

/-- Identification of Hilbert points is equivalent to an isomorphism of closed
subspaces over `X_T`. -/
theorem Rel_iff_overIso {f : X ⟶ B} {σ : SchemeOver B}
    (p q : Point f σ) :
    Rel p q ↔ Nonempty (Over.mk p.subspace.ι ≅ Over.mk q.subspace.ι) :=
  sorry

/-- Ideal-sheaf equality is an equivalence relation on Hilbert points. -/
theorem rel_isEquivalence (f : X ⟶ B) (σ : SchemeOver B) :
    Equivalence (fun p q : Point f σ ↦ Rel p q) :=
  sorry

/-- The setoid of Hilbert points modulo equal ideal sheaves. -/
def setoid (f : X ⟶ B) (σ : SchemeOver B) :
    Setoid (Point f σ) where
  r := Rel
  iseqv := rel_isEquivalence f σ

/-- Pullback preserves ideal-sheaf identification of Hilbert points. -/
theorem setoid_rel_pullback (f : X ⟶ B)
    {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    ∀ (p q : Point f σ),
      (setoid f σ).r p q → (setoid f τ).r (p.pullback h) (q.pullback h) :=
  sorry

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
