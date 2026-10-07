module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_13_1
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# The Grothendieck Hilbert functor on algebraic spaces

This module constructs the contravariant Hilbert functor of a finite-presentation
morphism of algebraic spaces. A test scheme `T` over `B` is sent to the set of
closed subspaces `Z ⊂ X_T` for which `Z ⟶ T` is of finite presentation, flat,
and proper, identified when they have the same ideal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver fiber fiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A closed subspace `Z ⊂ X_T` whose structure morphism `Z ⟶ T` is of finite
presentation, flat, and proper. -/
structure Point (f : X ⟶ B) (σ : SchemesOver B) [FinitePresentation f] where
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
def ofι (f : X ⟶ B) (σ : SchemesOver B) [FinitePresentation f]
    {Z : AlgebraicSpace S} (i : Z ⟶ fiber f σ) [IsClosedImmersion i]
    (isFinitePresentation : FinitePresentation (i ≫ pullback.snd f σ.hom))
    (isFlat : Flat (i ≫ pullback.snd f σ.hom))
    (isProper : Proper (i ≫ pullback.snd f σ.hom)) : Point f σ where
  subspace := ClosedSubspace.ofι i
  isFinitePresentation := isFinitePresentation
  isFlat := isFlat
  isProper := isProper

/-- The structure morphism `Z ⟶ T` of a Hilbert point. -/
def structureMap {f : X ⟶ B} {σ : SchemesOver B} [FinitePresentation f]
    (p : Point f σ) : p.subspace.X ⟶ (ofOverFunctor S).obj σ.left :=
  p.subspace.ι ≫ pullback.snd f σ.hom

/-- A Hilbert point is a closed subspace `Z ⊂ X_T` with `Z ⟶ T` of finite
presentation, flat, and proper. -/
theorem spec {f : X ⟶ B} {σ : SchemesOver B} [FinitePresentation f]
    (p : Point f σ) :
    IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
      Flat p.structureMap ∧ Proper p.structureMap :=
  sorry

/-- Pull back a Hilbert point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {σ τ : SchemesOver B} [FinitePresentation f]
    (p : Point f σ) (h : τ ⟶ σ) : Point f τ where
  subspace := p.subspace.inverseImage (fiberMap f h)
  isFinitePresentation := sorry
  isFlat := sorry
  isProper := sorry

/-- The closed subspace of a pulled-back Hilbert point is the inverse image
along `fiberMap`. -/
theorem pullback_subspace {f : X ⟶ B} {σ τ : SchemesOver B}
    [FinitePresentation f] (p : Point f σ) (h : τ ⟶ σ) :
    (p.pullback h).subspace = p.subspace.inverseImage (fiberMap f h) :=
  sorry

end Point

/-- Two Hilbert points are identified when they have the same ideal sheaf. -/
def Rel {f : X ⟶ B} {σ : SchemesOver B} [FinitePresentation f]
    (p q : Point f σ) : Prop :=
  p.subspace.idealSheaf = q.subspace.idealSheaf

/-- Identification of Hilbert points is equality of ideal sheaves. -/
theorem Rel_iff_idealSheaf {f : X ⟶ B} {σ : SchemesOver B}
    [FinitePresentation f] (p q : Point f σ) :
    Rel p q ↔ p.subspace.idealSheaf = q.subspace.idealSheaf :=
  sorry

/-- Identification of Hilbert points is equivalent to an isomorphism of closed
subspaces over `X_T`. -/
theorem Rel_iff_overIso {f : X ⟶ B} {σ : SchemesOver B}
    [FinitePresentation f] (p q : Point f σ) :
    Rel p q ↔ Nonempty (Over.mk p.subspace.ι ≅ Over.mk q.subspace.ι) :=
  sorry

/-- Ideal-sheaf equality is an equivalence relation on Hilbert points. -/
theorem rel_isEquivalence (f : X ⟶ B) [FinitePresentation f] (σ : SchemesOver B) :
    Equivalence (fun p q : Point f σ ↦ Rel p q) :=
  sorry

/-- The setoid of Hilbert points modulo equal ideal sheaves. -/
def setoid (f : X ⟶ B) [FinitePresentation f] (σ : SchemesOver B) :
    Setoid (Point f σ) where
  r := Rel
  iseqv := rel_isEquivalence f σ

/-- Pullback preserves ideal-sheaf identification of Hilbert points. -/
theorem setoid_rel_pullback (f : X ⟶ B) [FinitePresentation f]
    {σ τ : SchemesOver B} (h : τ ⟶ σ) :
    ∀ (p q : Point f σ),
      (setoid f σ).r p q → (setoid f τ).r (p.pullback h) (q.pullback h) :=
  sorry

/-- Pullback along the identity induces the identity on identified Hilbert
classes. -/
theorem hilbert_map_id (f : X ⟶ B) [FinitePresentation f]
    (σ : (SchemesOver B)ᵒᵖ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback (𝟙 σ).unop)
        (setoid_rel_pullback f (𝟙 σ).unop)) =
      𝟙 (_root_.Quotient (setoid f σ.unop)) :=
  sorry

/-- Pullback along a composite induces the composite of the pullback maps on
Hilbert classes. -/
theorem hilbert_map_comp (f : X ⟶ B) [FinitePresentation f]
    {σ τ ρ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
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
def hilbert (f : X ⟶ B) [FinitePresentation f] :
    (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (setoid f σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback h.unop)
        (setoid_rel_pullback f h.unop))
  map_id := hilbert_map_id f
  map_comp := hilbert_map_comp f

/-- The value of the Hilbert functor is the setoid quotient of Hilbert points by
equal ideal sheaves. -/
theorem hilbert_obj (f : X ⟶ B) [FinitePresentation f] (σ : SchemesOver B) :
    (hilbert f).obj (op σ) = _root_.Quotient (setoid f σ) :=
  sorry

/-- The Hilbert functor acts on a morphism by pullback of Hilbert points. -/
theorem hilbert_map (f : X ⟶ B) [FinitePresentation f]
    {σ τ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (hilbert f).map h =
      TypeCat.ofHom
        (_root_.Quotient.map (fun p : Point f σ.unop ↦ p.pullback h.unop)
          (setoid_rel_pullback f h.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
