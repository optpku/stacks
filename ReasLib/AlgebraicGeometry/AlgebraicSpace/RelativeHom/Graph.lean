/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.MorphismFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Graph
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

/-!
# Graph of a relative morphism as a Hilbert point

The graph of a morphism `f : Z_T ⟶ X_T` over `T` is the closed subspace
`Γ_f ⊂ (Z ×_B X)_T`. Under the standing hypotheses this yields a natural
transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (fiber fiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- The structure morphism `(Z ×_B X) ⟶ B`. -/
abbrev productHom (z : Z ⟶ B) (x : X ⟶ B) : pullback z x ⟶ B :=
  pullback.fst z x ≫ z

-- The private map is unfolded by the exposed product comparison.
set_option backward.privateInPublic true in
/-- The map between pullbacks over `Z` induced by swapping the factors of `T ×_B Z`. -/
private abbrev productFiberIso_symmetryMap (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B) :
    pullback (pullback.fst z x) (pullback.snd σ.hom z) ⟶
      pullback (pullback.fst z x) (pullback.fst z σ.hom) :=
  pullback.map (pullback.fst z x) (pullback.snd σ.hom z)
    (pullback.fst z x) (pullback.fst z σ.hom)
    (𝟙 (pullback z x)) (pullbackSymmetry σ.hom z).hom (𝟙 Z)
    ((Category.comp_id (pullback.fst z x)).trans (Category.id_comp (pullback.fst z x)).symm)
    ((Category.comp_id (pullback.snd σ.hom z)).trans
      (pullbackSymmetry_hom_comp_fst σ.hom z).symm)

-- The exposed comparison uses the private concrete pullback map in its definition.
set_option backward.privateInPublic true in
/-- The canonical identification `(Z_T ×_T X_T) ≅ (Z ×_B X)_T`. -/
def productFiberIso (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B) :
    pullback (pullback.fst σ.hom z) (pullback.fst σ.hom x) ≅
      fiber (productHom z x) σ :=
  pullbackRightPullbackFstIso σ.hom x (pullback.fst σ.hom z) ≪≫
    pullback.congrHom
      (pullback.condition :
        pullback.fst σ.hom z ≫ σ.hom = pullback.snd σ.hom z ≫ z)
      (rfl : x = x) ≪≫
    (pullbackRightPullbackFstIso z x (pullback.snd σ.hom z)).symm ≪≫
    pullbackSymmetry (pullback.snd σ.hom z) (pullback.fst z x) ≪≫
    asIso (productFiberIso_symmetryMap z x σ) ≪≫
    pullbackRightPullbackFstIso z σ.hom (pullback.fst z x)

/-- The first projection of `productFiberIso.hom` recovers the map to `Z`. -/
theorem productFiberIso_hom_fst (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B) :
    (productFiberIso z x σ).hom ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x =
      pullback.fst (pullback.fst σ.hom z) (pullback.fst σ.hom x) ≫
        pullback.snd σ.hom z :=
  sorry

/-- The second projection of `productFiberIso.hom` recovers the map to `T`. -/
theorem productFiberIso_hom_snd (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B) :
    (productFiberIso z x σ).hom ≫ pullback.snd (productHom z x) σ.hom =
      pullback.fst (pullback.fst σ.hom z) (pullback.fst σ.hom x) ≫
        pullback.fst σ.hom z :=
  sorry

/-- The graph of a relative morphism, transported to `(Z ×_B X)_T`. -/
def graphImmersion (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    pullback σ.hom z ⟶ fiber (productHom z x) σ :=
  pullback.graph (pullback.fst σ.hom z) (pullback.fst σ.hom x) b.left (Over.w b) ≫
    (productFiberIso z x σ).hom

/-- The composite of the graph immersion with the projection to `T` is
`Z_T ⟶ T`. -/
theorem graphImmersion_fst (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    graphImmersion z x σ b ≫ pullback.snd (productHom z x) σ.hom =
      pullback.fst σ.hom z :=
  sorry

/-- The composite of the graph immersion with the projection to `X` recovers
the original morphism. -/
theorem graphImmersion_snd (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    graphImmersion z x σ b ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.snd z x =
      b.left ≫ pullback.snd σ.hom x :=
  sorry

/-- The graph of a relative morphism is a closed immersion when `X ⟶ B` is
separated. -/
instance instIsClosedImmersion_graphImmersion (z : Z ⟶ B) (x : X ⟶ B)
    (σ : SchemeOver B) (b : BaseChangeMorphism z x σ.hom) [Separated x] :
    IsClosedImmersion (graphImmersion z x σ b) :=
  sorry

/-- A closed subspace of `(Z ×_B X)_T` whose structure morphism to `T` is of
finite presentation, flat, and proper. -/
abbrev FiberPoint (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B) :=
  Hilbert.Point (productHom z x) σ

/-- Two closed subspaces of a product fibre represent the same Hilbert point when
their ideal sheaves agree. -/
abbrev Rel {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemeOver B}
    (p q : FiberPoint z x σ) : Prop := Hilbert.Rel p q

/-- The structure morphism of the graph is of finite presentation, flat, and proper. -/
theorem graphPoint_properties (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (b : BaseChangeMorphism z x σ.hom) :
    FinitePresentation (graphImmersion z x σ b ≫ pullback.snd (productHom z x) σ.hom) ∧
      Flat (graphImmersion z x σ b ≫ pullback.snd (productHom z x) σ.hom) ∧
      Proper (graphImmersion z x σ b ≫ pullback.snd (productHom z x) σ.hom) := sorry

/-- The graph of a relative morphism, as a fibre point of `(Z ×_B X)_T`. -/
def graphPoint (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (b : BaseChangeMorphism z x σ.hom) : FiberPoint z x σ where
  subspace := ClosedSubspace.ofι (graphImmersion z x σ b)
  isFinitePresentation := (graphPoint_properties z x σ b).1
  isFlat := (graphPoint_properties z x σ b).2.1
  isProper := (graphPoint_properties z x σ b).2.2

/-- The closed subspace of `graphPoint` is the graph immersion. -/
theorem graphPoint_subspace (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (b : BaseChangeMorphism z x σ.hom) :
    (graphPoint z x σ b).subspace = ClosedSubspace.ofι (graphImmersion z x σ b) :=
  sorry

/-- Restriction of a graph along `T' ⟶ T` is the pullback of the graph point. -/
theorem graphPoint_pullback (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemeOver B}
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (h : τ ⟶ σ) (b : BaseChangeMorphism z x σ.hom) :
    Rel (graphPoint z x τ (restrict z x h b)) ((graphPoint z x σ b).pullback h) :=
  sorry

/-- The Hilbert functor of the relative product. -/
abbrev hilb (z : Z ⟶ B) (x : X ⟶ B) : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) :=
  Hilbert.functor (productHom z x)

/-- The Hilbert functor of the relative product agrees with its finite-presentation
specialization whenever the product morphism is of finite presentation. -/
def hilbToHilbert {S : Scheme.{u}} {Z B X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) [FinitePresentation (productHom z x)] :
    hilb z x ⟶ Hilbert.hilbert (productHom z x) := 𝟙 (hilb z x)

/-- The graph transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}`. -/
def graph (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    mor z x ⟶ hilb z x where
  app σ :=
    TypeCat.ofHom fun b ↦
      _root_.Quotient.mk (Hilbert.setoid (productHom z x) σ.unop) (graphPoint z x σ.unop b)
  naturality := sorry

/-- The component of the graph transformation at a scheme over `B` sends a
morphism to the class of its graph. -/
theorem graph_app (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] (σ : SchemeOver B)
    (b : BaseChangeMorphism z x σ.hom) :
    (graph z x).app (op σ) b =
      _root_.Quotient.mk (Hilbert.setoid (productHom z x) σ) (graphPoint z x σ b) :=
  sorry

/-- Taking graphs is injective on morphisms over every test scheme. -/
theorem graph_app_injective (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] (σ : SchemeOver B) :
    Function.Injective fun b ↦ (graph z x).app (op σ) b := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
