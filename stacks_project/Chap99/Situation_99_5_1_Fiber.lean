/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Fibres of a morphism of algebraic spaces along schemes over the base

A test scheme `T` over an algebraic space `B` is a costructured arrow of
`ofOverFunctor S`. The fibre `X_T` is the pullback of `f : X ⟶ B` along the
structure map of the test object, and a morphism of test schemes induces a
base-change map of fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Schemes over an algebraic space `B`, as costructured arrows of `ofOverFunctor S`. -/
abbrev SchemesOver (B : AlgebraicSpace S) :=
  CostructuredArrow (ofOverFunctor S) B

/-- The base change `X_T = T ×_B X` of `X` along a scheme `T` over `B`. -/
def fiber (f : X ⟶ B) (σ : SchemesOver B) : AlgebraicSpace S :=
  pullback f σ.hom

/-- The fibre of `f` along `σ` is the categorical pullback of `f` and `σ.hom`. -/
theorem fiber_eq (f : X ⟶ B) (σ : SchemesOver B) :
    fiber f σ = pullback f σ.hom := sorry

/-- The projection `X_T ⟶ T` of the fibre product, as a morphism of algebraic spaces. -/
def fiberToBase (f : X ⟶ B) (σ : SchemesOver B) :
    fiber f σ ⟶ (ofOverFunctor S).obj σ.left :=
  pullback.snd f σ.hom

/-- The projection `fiberToBase f σ` is `pullback.snd f σ.hom`. -/
theorem fiberToBase_eq (f : X ⟶ B) (σ : SchemesOver B) :
    fiberToBase f σ = pullback.snd f σ.hom := sorry

/-- The canonical map `X_T ⟶ X_{T'}` induced by a morphism of schemes over `B`. -/
def fiberMap (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiber f σ ⟶ fiber f τ :=
  pullback.map f σ.hom f τ.hom (𝟙 X) ((ofOverFunctor S).map h.left) (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id σ.hom).trans (CostructuredArrow.w h).symm)

/-- The map `fiberMap f h` commutes with the projections to `X`. -/
theorem fiberMap_fst (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.fst f τ.hom = pullback.fst f σ.hom := sorry

/-- The map `fiberMap f h` commutes with the projections to the varying base. -/
theorem fiberMap_snd (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.snd f τ.hom =
      pullback.snd f σ.hom ≫ (ofOverFunctor S).map h.left := sorry

/-- The identity morphism of a scheme over `B` induces the identity on fibres. -/
theorem fiberMap_id (f : X ⟶ B) (σ : SchemesOver B) :
    fiberMap f (𝟙 σ) = 𝟙 (fiber f σ) := sorry

/-- Fibre maps are functorial in morphisms of schemes over `B`. -/
theorem fiberMap_comp (f : X ⟶ B) {σ τ ρ : SchemesOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    fiberMap f (h ≫ k) = fiberMap f h ≫ fiberMap f k := sorry

/-- The identity morphism of schemes over `B` induces an isomorphism of fibres,
with forward map `fiberMap f (𝟙 σ)` and inverse the mediating map of the
identity cone. -/
def fiberMapIdIso (f : X ⟶ B) (σ : SchemesOver B) : fiber f σ ≅ fiber f σ where
  hom := fiberMap f (𝟙 σ)
  inv := pullback.lift (pullback.fst f σ.hom) (pullback.snd f σ.hom) pullback.condition
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack

