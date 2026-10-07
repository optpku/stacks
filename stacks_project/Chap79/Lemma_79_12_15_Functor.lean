module

public import stacks_project.Chap79.Lemma_79_12_7_Hom
public import stacks_project.Chap79.«79_12_14_1_WithSection»

/-!
# Finite-part functor of pairs containing a section graph

A section `σ` of `f : X ⟶ Y` determines the subfunctor `(X/Y, σ)_fin` of
`(X/Y)_fin` whose pairs `(a, Z)` have the graph `(1_T, σ ∘ a)` factoring
through `Z`, together with the inclusion `t : (X/Y, σ)_fin ⟶ (X/Y)_fin`.

The scheme-level pairs reuse `FinitePart.Point` from Lemma 79.12.7, whose
opens are algebraic-space open subspaces, so this owner does not depend on
the points-space topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace WithSection

/-- A finite-part pair `(a, Z)` over a scheme `T` through which the graph of `σ`
factors. -/
structure Point (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) (T : Over S)
    extends FinitePart.Point f T where
  /-- The graph `(1_T, σ ∘ a)` factors through `Z`. -/
  factors : ∃ ℓ : ofOver T ⟶ Z.X, ℓ ≫ Z.ι = sectionGraph a f σ hσ

/-- Build a with-section pair from a finite-part pair through which the graph of
`σ` factors. -/
def Point.of {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S}
    (p : FinitePart.Point f T)
    (h : ∃ ℓ : ofOver T ⟶ p.Z.X, ℓ ≫ p.Z.ι = sectionGraph p.a f σ hσ) :
    Point f σ hσ T where
  toPoint := p
  factors := h

/-- A with-section pair is a finite-part pair whose open subspace contains the
graph of `σ`. -/
theorem Point.spec {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} {T : Over S}
    (p : Point f σ hσ T) :
    IsOpenImmersion p.Z.ι ∧ IsFinite (p.Z.ι ≫ pullback.fst p.a f) ∧
      ∃ ℓ : ofOver T ⟶ p.Z.X, ℓ ≫ p.Z.ι = sectionGraph p.a f σ hσ :=
  sorry

/-- Base change along `h : T' ⟶ T` preserves the section-graph condition. -/
theorem Point.restrict_factors {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y}
    {T T' : Over S} (p : Point f σ hσ T) (h : T' ⟶ T) :
    ∃ ℓ : ofOver T' ⟶ (p.toPoint.restrict h).Z.X,
      ℓ ≫ (p.toPoint.restrict h).Z.ι =
        sectionGraph (ofOverMap h ≫ p.a) f σ hσ :=
  sorry

/-- Base change of a with-section pair along `h : T' ⟶ T`. -/
def Point.restrict {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y}
    {T T' : Over S} (p : Point f σ hσ T) (h : T' ⟶ T) :
    Point f σ hσ T' where
  toPoint := p.toPoint.restrict h
  factors := Point.restrict_factors p h

/-- The type of with-section pairs over a scheme `T` is `u`-small. -/
instance instSmall_point {f : X ⟶ Y} {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y}
    {T : Over S} : Small.{u} (Point f σ hσ T) :=
  sorry

end WithSection

/-- The finite-part-with-section functor `(X/Y, σ)_fin : (Over S)ᵒᵖ ⥤ Type u`. -/
def withSectionFunctor (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (WithSection.Point f σ hσ T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (WithSection.Point f σ hσ T'.unop)
        (((equivShrink (WithSection.Point f σ hσ T.unop)).symm p).restrict h.unop)
  map_id := sorry
  map_comp := sorry

/-- Values of the with-section functor are equivalent to with-section pairs. -/
def withSectionFunctor_obj_equiv (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : Over S) :
    (withSectionFunctor f σ hσ).obj (op T) ≃ WithSection.Point f σ hσ T :=
  (equivShrink (WithSection.Point f σ hσ T)).symm

/-- The inclusion `t : (X/Y, σ)_fin ⟶ (X/Y)_fin` forgetting the section-graph
condition. -/
def withSectionι (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    withSectionFunctor f σ hσ ⟶ functor f where
  app T :=
    TypeCat.ofHom fun p ↦
      equivShrink (Point f T.unop)
        (((equivShrink (WithSection.Point f σ hσ T.unop)).symm p).toPoint)
  naturality := sorry

/-- Components of `withSectionι` send a with-section pair to the underlying
finite-part pair. -/
theorem withSectionι_app (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (T : (Over S)ᵒᵖ) (p : (withSectionFunctor f σ hσ).obj T) :
    (withSectionι f σ hσ).app T p =
      equivShrink (Point f T.unop)
        (((equivShrink (WithSection.Point f σ hσ T.unop)).symm p).toPoint) :=
  sorry

/-- The inclusion `t` forgets the condition that the section graph factors
through `Z`. -/
theorem withSectionι_spec (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T : Over S} (p : WithSection.Point f σ hσ T) :
    (withSectionι f σ hσ).app (op T)
        ((withSectionFunctor_obj_equiv f σ hσ T).symm p) =
      (functor_obj_equiv f T).symm p.toPoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
