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
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»
public import stacks_project.Chap99.Lemma_99_16_1_Pullback

/-!
# Fibre maps of a morphism of algebraic spaces along schemes over the base

A test scheme over an algebraic space `B` is a costructured arrow of
`ofOverFunctor S`. A morphism of test schemes induces the base-change map of
fibres `X_T ⟶ X_{T'}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical map `X_T ⟶ X_{T'}` induced by a morphism of schemes over `B`. -/
def fiberMap (f : X ⟶ B) {σ τ : SchemeOver B} (h : σ ⟶ τ) :
    pullback f σ.hom ⟶ pullback f τ.hom :=
  baseChangeSpaceMap f ((ofOverFunctor S).map h.left) (CostructuredArrow.w h)

/-- The map `fiberMap f h` commutes with the projections to `X`. -/
theorem fiberMap_fst (f : X ⟶ B) {σ τ : SchemeOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.fst f τ.hom = pullback.fst f σ.hom :=
  pullback.lift_fst _ _ _

/-- The map `fiberMap f h` commutes with the projections to the varying base. -/
theorem fiberMap_snd (f : X ⟶ B) {σ τ : SchemeOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.snd f τ.hom =
      pullback.snd f σ.hom ≫ (ofOverFunctor S).map h.left :=
  pullback.lift_snd _ _ _

/-- The identity morphism of a scheme over `B` induces the identity on fibres. -/
theorem fiberMap_id_eq (f : X ⟶ B) (σ : SchemeOver B) :
    fiberMap f (𝟙 σ) = 𝟙 (pullback f σ.hom) :=
  pullback.hom_ext
    ((pullback.lift_fst _ _ _).trans (Category.id_comp (pullback.fst f σ.hom)).symm)
    (((pullback.lift_snd _ _ _).trans
        ((congrArg (fun i => pullback.snd f σ.hom ≫ i)
            (CategoryTheory.Functor.map_id yoneda σ.left)).trans
          (Category.comp_id (pullback.snd f σ.hom)))).trans
      (Category.id_comp (pullback.snd f σ.hom)).symm)

/-- Fibre maps are functorial in morphisms of schemes over `B`. -/
theorem fiberMap_comp_eq (f : X ⟶ B) {σ τ ρ : SchemeOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    fiberMap f (h ≫ k) = fiberMap f h ≫ fiberMap f k :=
  pullback.hom_ext
    ((pullback.lift_fst _ _ _).trans
      (Eq.symm
        ((Category.assoc (fiberMap f h) (fiberMap f k)
            (pullback.fst f ρ.hom)).symm.trans
          ((congrArg (fun φ => fiberMap f h ≫ φ) (pullback.lift_fst _ _ _)).trans
            (pullback.lift_fst _ _ _)))))
    ((pullback.lift_snd _ _ _).trans
      ((congrArg (fun i => pullback.snd f σ.hom ≫ i)
          (CategoryTheory.Functor.map_comp yoneda h.left k.left)).trans
        ((Category.assoc (pullback.snd f σ.hom) ((ofOverFunctor S).map h.left)
            ((ofOverFunctor S).map k.left)).symm.trans
          ((congrArg (fun φ => φ ≫ (ofOverFunctor S).map k.left)
              (Eq.symm (pullback.lift_snd _ _ _))).trans
            ((Category.assoc (fiberMap f h) (pullback.snd f τ.hom)
                ((ofOverFunctor S).map k.left)).trans
              ((congrArg (fun φ => fiberMap f h ≫ φ)
                  (Eq.symm (pullback.lift_snd _ _ _))).trans
                (Category.assoc (fiberMap f h) (fiberMap f k)
                  (pullback.snd f ρ.hom))))))))

end AlgebraicGeometry.AlgebraicSpace.Complexes
