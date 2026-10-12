/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap97.«97_10_0_1_RelativeHom»
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# Relative morphisms on schemes over `B`

The functor `Mor_B(Z, X)` on `(Sch/B)^op`, sending a scheme `T` over `B` to
the type of morphisms `Z_T ⟶ X_T` over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- The comparison `T' ×_B Z ⟶ T ×_B Z` induced by a morphism of schemes over `B`. -/
def baseChangeMap (z : Z ⟶ B) {σ τ : SchemesOver B} (h : τ ⟶ σ) :
    pullback τ.hom z ⟶ pullback σ.hom z :=
  pullback.map τ.hom z σ.hom z ((ofOverFunctor S).map h.left) (𝟙 Z) (𝟙 B)
    ((Category.comp_id τ.hom).trans (CostructuredArrow.w h).symm)
    ((Category.comp_id z).trans (Category.id_comp z).symm)

/-- `baseChangeMap` commutes with the projections to the varying test object. -/
theorem baseChangeMap_fst (z : Z ⟶ B) {σ τ : SchemesOver B} (h : τ ⟶ σ) :
    baseChangeMap z h ≫ pullback.fst σ.hom z =
      pullback.fst τ.hom z ≫ (ofOverFunctor S).map h.left :=
  sorry

/-- `baseChangeMap` commutes with the projections to `Z`. -/
theorem baseChangeMap_snd (z : Z ⟶ B) {σ τ : SchemesOver B} (h : τ ⟶ σ) :
    baseChangeMap z h ≫ pullback.snd σ.hom z = pullback.snd τ.hom z :=
  sorry

/-- The maps `pr₀` and `baseChangeMap h ≫ b.left ≫ pr₁` agree over `B`. -/
theorem restrict_lift_condition (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemesOver B}
    (h : τ ⟶ σ) (b : BaseChangeMorphism z x σ.hom) :
    pullback.fst τ.hom z ≫ τ.hom =
      (baseChangeMap z h ≫ b.left ≫ pullback.snd σ.hom x) ≫ x :=
  sorry

/-- The mediating morphism of `restrict` projects to the test object as
`pullback.fst τ.hom z`. -/
theorem restrict_fst (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemesOver B}
    (h : τ ⟶ σ) (b : BaseChangeMorphism z x σ.hom) :
    pullback.lift (pullback.fst τ.hom z)
        (baseChangeMap z h ≫ b.left ≫ pullback.snd σ.hom x)
        (restrict_lift_condition z x h b) ≫
      pullback.fst τ.hom x =
      pullback.fst τ.hom z :=
  sorry

/-- Restriction of a morphism `Z_T ⟶ X_T` over `T` along `T' ⟶ T` over `B`. -/
def restrict (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemesOver B} (h : τ ⟶ σ)
    (b : BaseChangeMorphism z x σ.hom) : BaseChangeMorphism z x τ.hom :=
  Over.homMk
    (pullback.lift (pullback.fst τ.hom z)
      (baseChangeMap z h ≫ b.left ≫ pullback.snd σ.hom x)
      (restrict_lift_condition z x h b))
    (restrict_fst z x h b)

/-- Restriction along the identity morphism of a scheme over `B` is the identity. -/
theorem mor_map_id (z : Z ⟶ B) (x : X ⟶ B) (σ : (SchemesOver B)ᵒᵖ) :
    TypeCat.ofHom (restrict z x (𝟙 σ).unop) =
      𝟙 (BaseChangeMorphism z x σ.unop.hom) :=
  sorry

/-- Restriction along a composite morphism of schemes over `B` is the composite
restriction. -/
theorem mor_map_comp (z : Z ⟶ B) (x : X ⟶ B) {σ τ ρ : (SchemesOver B)ᵒᵖ}
    (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom (restrict z x (h ≫ k).unop) =
      TypeCat.ofHom (restrict z x h.unop) ≫ TypeCat.ofHom (restrict z x k.unop) :=
  sorry

/-- The relative-Hom functor `Mor_B(Z, X)` on schemes over `B`. -/
def mor (z : Z ⟶ B) (x : X ⟶ B) : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := BaseChangeMorphism z x σ.unop.hom
  map h := TypeCat.ofHom (restrict z x h.unop)
  map_id := mor_map_id z x
  map_comp := mor_map_comp z x

/-- Evaluating `Mor_B(Z, X)` at a scheme over `B` recovers morphisms `Z_T ⟶ X_T`
over `T`. -/
theorem mor_obj (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemesOver B) :
    (mor z x).obj (op σ) = BaseChangeMorphism z x σ.hom :=
  sorry

/-- The relative-Hom functor acts on a morphism of schemes over `B` by restriction. -/
theorem mor_map (z : Z ⟶ B) (x : X ⟶ B) {σ τ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (mor z x).map h = TypeCat.ofHom (restrict z x h.unop) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
