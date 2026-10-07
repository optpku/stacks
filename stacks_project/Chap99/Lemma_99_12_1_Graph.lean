module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap67.Lemma_67_4_4_Pullback
public import stacks_project.Chap67.Lemma_67_4_6
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap67.Lemma_67_40_3_Pullback
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap99.«99_9_1_1_Functor»
public import stacks_project.Chap99.Lemma_99_12_1_Mor

/-!
# Graph of a relative morphism as a Hilbert point

The graph of a morphism `f : Z_T ⟶ X_T` over `T` is the closed subspace
`Γ_f ⊂ (Z ×_B X)_T`. Under the standing hypotheses this yields a natural
transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver fiber fiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- The structure morphism `(Z ×_B X) ⟶ B`. -/
abbrev productHom (z : Z ⟶ B) (x : X ⟶ B) : pullback z x ⟶ B :=
  pullback.fst z x ≫ z

/-- The comparison identifying `(T ×_B Z) ×_Z (Z ×_B X)` with
`(Z ×_B X) ×_Z (Z ×_B T)` by swapping the `Z`-factor. -/
abbrev fiberIso_symmetryMap (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    pullback (pullback.fst z x) (pullback.snd σ.hom z) ⟶
      pullback (pullback.fst z x) (pullback.fst z σ.hom) :=
  pullback.map (pullback.fst z x) (pullback.snd σ.hom z)
    (pullback.fst z x) (pullback.fst z σ.hom)
    (𝟙 (pullback z x)) (pullbackSymmetry σ.hom z).hom (𝟙 Z)
    ((Category.comp_id (pullback.fst z x)).trans (Category.id_comp (pullback.fst z x)).symm)
    ((Category.comp_id (pullback.snd σ.hom z)).trans
      (pullbackSymmetry_hom_comp_fst σ.hom z).symm)

/-- The canonical identification `(Z_T ×_T X_T) ≅ (Z ×_B X)_T`. -/
def fiberIso (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    pullback (pullback.fst σ.hom z) (pullback.fst σ.hom x) ≅
      fiber (productHom z x) σ :=
  pullbackRightPullbackFstIso σ.hom x (pullback.fst σ.hom z) ≪≫
    pullback.congrHom
      (pullback.condition :
        pullback.fst σ.hom z ≫ σ.hom = pullback.snd σ.hom z ≫ z)
      (rfl : x = x) ≪≫
    (pullbackRightPullbackFstIso z x (pullback.snd σ.hom z)).symm ≪≫
    pullbackSymmetry (pullback.snd σ.hom z) (pullback.fst z x) ≪≫
    asIso (fiberIso_symmetryMap z x σ) ≪≫
    pullbackRightPullbackFstIso z σ.hom (pullback.fst z x)

/-- The first projection of `fiberIso.hom` recovers the map to `Z`. -/
theorem fiberIso_hom_fst (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    (fiberIso z x σ).hom ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x =
      pullback.fst (pullback.fst σ.hom z) (pullback.fst σ.hom x) ≫
        pullback.snd σ.hom z :=
  sorry

/-- The second projection of `fiberIso.hom` recovers the map to `T`. -/
theorem fiberIso_hom_snd (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    (fiberIso z x σ).hom ≫ pullback.snd (productHom z x) σ.hom =
      pullback.fst (pullback.fst σ.hom z) (pullback.fst σ.hom x) ≫
        pullback.fst σ.hom z :=
  sorry

/-- The graph of a relative morphism, transported to `(Z ×_B X)_T`. -/
def graphImmersion (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    pullback σ.hom z ⟶ fiber (productHom z x) σ :=
  pullback.graph (pullback.fst σ.hom z) (pullback.fst σ.hom x) b.left (Over.w b) ≫
    (fiberIso z x σ).hom

/-- The composite of the graph immersion with the projection to `T` is
`Z_T ⟶ T`. -/
theorem graphImmersion_fst (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    graphImmersion z x σ b ≫ pullback.snd (productHom z x) σ.hom =
      pullback.fst σ.hom z :=
  sorry

/-- The composite of the graph immersion with the projection to `X` recovers
the original morphism. -/
theorem graphImmersion_snd (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    graphImmersion z x σ b ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.snd z x =
      b.left ≫ pullback.snd σ.hom x :=
  sorry

/-- The graph of a relative morphism is a closed immersion when `X ⟶ B` is
separated. -/
instance instIsClosedImmersion_graphImmersion (z : Z ⟶ B) (x : X ⟶ B)
    (σ : SchemesOver B) (b : BaseChangeMorphism z x σ.hom) [Separated x] :
    IsClosedImmersion (graphImmersion z x σ b) :=
  sorry

/-- A closed subspace of `(Z ×_B X)_T` whose structure morphism to `T` is of
finite presentation, flat, and proper. -/
structure FiberPoint (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) where
  /-- The closed subspace of the base change `(Z ×_B X)_T`. -/
  subspace : ClosedSubspace (fiber (productHom z x) σ)
  /-- The structure morphism `Z' ⟶ T` is of finite presentation. -/
  isFinitePresentation :
    FinitePresentation (subspace.ι ≫ pullback.snd (productHom z x) σ.hom)
  /-- The structure morphism `Z' ⟶ T` is flat. -/
  isFlat : Flat (subspace.ι ≫ pullback.snd (productHom z x) σ.hom)
  /-- The structure morphism `Z' ⟶ T` is proper. -/
  isProper : Proper (subspace.ι ≫ pullback.snd (productHom z x) σ.hom)

namespace FiberPoint

/-- Construct a fibre point from a closed immersion into `(Z ×_B X)_T` whose
composite to `T` is of finite presentation, flat, and proper. -/
def ofι (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) {W : AlgebraicSpace S}
    (i : W ⟶ fiber (productHom z x) σ) [IsClosedImmersion i]
    (isFinitePresentation : FinitePresentation (i ≫ pullback.snd (productHom z x) σ.hom))
    (isFlat : Flat (i ≫ pullback.snd (productHom z x) σ.hom))
    (isProper : Proper (i ≫ pullback.snd (productHom z x) σ.hom)) :
    FiberPoint z x σ where
  subspace := ClosedSubspace.ofι i
  isFinitePresentation := isFinitePresentation
  isFlat := isFlat
  isProper := isProper

/-- The structure morphism `Z' ⟶ T` of a fibre point. -/
def structureMap {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p : FiberPoint z x σ) : p.subspace.X ⟶ (ofOverFunctor S).obj σ.left :=
  p.subspace.ι ≫ pullback.snd (productHom z x) σ.hom

/-- A fibre point is a closed subspace of `(Z ×_B X)_T` with structure morphism
of finite presentation, flat, and proper. -/
theorem spec {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B} (p : FiberPoint z x σ) :
    IsClosedImmersion p.subspace.ι ∧ FinitePresentation p.structureMap ∧
      Flat p.structureMap ∧ Proper p.structureMap :=
  sorry

/-- Pull back a fibre point along a morphism of schemes over `B`. -/
def pullback {z : Z ⟶ B} {x : X ⟶ B} {σ τ : SchemesOver B}
    (p : FiberPoint z x σ) (h : τ ⟶ σ) : FiberPoint z x τ where
  subspace := p.subspace.inverseImage (fiberMap (productHom z x) h)
  isFinitePresentation := sorry
  isFlat := sorry
  isProper := sorry

/-- The closed subspace of a pulled-back fibre point is the inverse image along
`fiberMap`. -/
theorem pullback_subspace {z : Z ⟶ B} {x : X ⟶ B} {σ τ : SchemesOver B}
    (p : FiberPoint z x σ) (h : τ ⟶ σ) :
    (p.pullback h).subspace = p.subspace.inverseImage (fiberMap (productHom z x) h) :=
  sorry

end FiberPoint

/-- Two fibre points are identified when they have the same ideal sheaf. -/
def Rel {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p q : FiberPoint z x σ) : Prop :=
  p.subspace.idealSheaf = q.subspace.idealSheaf

/-- Identification of fibre points is equality of ideal sheaves. -/
theorem Rel_iff_idealSheaf {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p q : FiberPoint z x σ) :
    Rel p q ↔ p.subspace.idealSheaf = q.subspace.idealSheaf :=
  sorry

/-- Ideal-sheaf equality is an equivalence relation on fibre points. -/
theorem rel_isEquivalence (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    Equivalence (fun p q : FiberPoint z x σ ↦ Rel p q) :=
  sorry

/-- The setoid of fibre points modulo equal ideal sheaves. -/
def setoid (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    Setoid (FiberPoint z x σ) where
  r := Rel
  iseqv := rel_isEquivalence z x σ

/-- Pullback preserves ideal-sheaf identification of fibre points. -/
theorem setoid_rel_pullback (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemesOver B}
    (h : τ ⟶ σ) :
    ∀ (p q : FiberPoint z x σ),
      (setoid z x σ).r p q → (setoid z x τ).r (p.pullback h) (q.pullback h) :=
  sorry

/-- The graph of a relative morphism, as a fibre point of `(Z ×_B X)_T`. -/
def graphPoint (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (b : BaseChangeMorphism z x σ.hom) : FiberPoint z x σ where
  subspace := ClosedSubspace.ofι (graphImmersion z x σ b)
  isFinitePresentation := sorry
  isFlat := sorry
  isProper := sorry

/-- The closed subspace of `graphPoint` is the graph immersion. -/
theorem graphPoint_subspace (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (b : BaseChangeMorphism z x σ.hom) :
    (graphPoint z x σ b).subspace = ClosedSubspace.ofι (graphImmersion z x σ b) :=
  sorry

/-- Restriction of a graph along `T' ⟶ T` is the pullback of the graph point. -/
theorem graphPoint_pullback (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemesOver B}
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (h : τ ⟶ σ) (b : BaseChangeMorphism z x σ.hom) :
    graphPoint z x τ (restrict z x h b) = (graphPoint z x σ b).pullback h :=
  sorry

/-- Pullback along the identity induces the identity on identified fibre
classes. -/
theorem hilb_map_id (z : Z ⟶ B) (x : X ⟶ B) (σ : (SchemesOver B)ᵒᵖ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : FiberPoint z x σ.unop ↦ p.pullback (𝟙 σ).unop)
        (setoid_rel_pullback z x (𝟙 σ).unop)) =
      𝟙 (_root_.Quotient (setoid z x σ.unop)) :=
  sorry

/-- Pullback along a composite induces the composite of the pullback maps on
fibre classes. -/
theorem hilb_map_comp (z : Z ⟶ B) (x : X ⟶ B)
    {σ τ ρ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : FiberPoint z x σ.unop ↦ p.pullback (h ≫ k).unop)
        (setoid_rel_pullback z x (h ≫ k).unop)) =
      TypeCat.ofHom
          (_root_.Quotient.map (fun p : FiberPoint z x σ.unop ↦ p.pullback h.unop)
            (setoid_rel_pullback z x h.unop)) ≫
        TypeCat.ofHom
          (_root_.Quotient.map (fun p : FiberPoint z x τ.unop ↦ p.pullback k.unop)
            (setoid_rel_pullback z x k.unop)) :=
  sorry

/-- The set-valued Hilbert functor `Hilb_{Z ×_B X / B}` of closed subspaces of
`(Z ×_B X)_T` that are of finite presentation, flat, and proper over the test
scheme, identified by equal ideal sheaves. -/
def hilb (z : Z ⟶ B) (x : X ⟶ B) : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (setoid z x σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : FiberPoint z x σ.unop ↦ p.pullback h.unop)
        (setoid_rel_pullback z x h.unop))
  map_id := hilb_map_id z x
  map_comp := hilb_map_comp z x

/-- The value of `hilb` is the setoid quotient of fibre points by equal ideal
sheaves. -/
theorem hilb_obj (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    (hilb z x).obj (op σ) = _root_.Quotient (setoid z x σ) :=
  sorry

/-- The Hilbert-style functor acts on a morphism by pullback of fibre points. -/
theorem hilb_map (z : Z ⟶ B) (x : X ⟶ B) {σ τ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (hilb z x).map h =
      TypeCat.ofHom
        (_root_.Quotient.map (fun p : FiberPoint z x σ.unop ↦ p.pullback h.unop)
          (setoid_rel_pullback z x h.unop)) :=
  sorry

/-- Convert a fibre point to a Hilbert point when the ambient morphism
`(Z ×_B X) ⟶ B` is of finite presentation. -/
def FiberPoint.toHilbert {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    [FinitePresentation (productHom z x)] (p : FiberPoint z x σ) :
    Hilbert.Point (productHom z x) σ where
  subspace := p.subspace
  isFinitePresentation := p.isFinitePresentation
  isFlat := p.isFlat
  isProper := p.isProper

/-- Conversion to Hilbert points preserves ideal-sheaf identification. -/
theorem toHilbert_rel (z : Z ⟶ B) (x : X ⟶ B) [FinitePresentation (productHom z x)]
    (σ : SchemesOver B) (p q : FiberPoint z x σ) :
    (setoid z x σ).r p q →
      (Hilbert.setoid (productHom z x) σ).r p.toHilbert q.toHilbert :=
  sorry

/-- Comparison of `hilb` with the finite-presentation Hilbert functor of
Situation 99.9, when `(Z ×_B X) ⟶ B` is of finite presentation. -/
def hilbToHilbert (z : Z ⟶ B) (x : X ⟶ B) [FinitePresentation (productHom z x)] :
    hilb z x ⟶ Hilbert.hilbert (productHom z x) where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : FiberPoint z x σ.unop ↦ FiberPoint.toHilbert p)
        (toHilbert_rel z x σ.unop))
  naturality := sorry

/-- The graph transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}`. -/
def graph (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    mor z x ⟶ hilb z x where
  app σ :=
    TypeCat.ofHom fun b ↦
      _root_.Quotient.mk (setoid z x σ.unop) (graphPoint z x σ.unop b)
  naturality := sorry

/-- The component of the graph transformation at a scheme over `B` sends a
morphism to the class of its graph. -/
theorem graph_app (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] (σ : SchemesOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    (graph z x).app (op σ) b =
      _root_.Quotient.mk (setoid z x σ) (graphPoint z x σ b) :=
  sorry

/-- The graph transformation is a monomorphism of functors. -/
instance graph.instMono (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    Mono (graph z x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
