/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The induced morphism of algebraic spaces over `B` preserves identities. -/
theorem SchemeOver.toOver_id (σ : SchemeOver B) :
    (Over.homMk ((ofOverFunctor S).map (𝟙 σ : σ ⟶ σ).left)
      (CostructuredArrow.w (𝟙 σ)) : Over.mk σ.hom ⟶ Over.mk σ.hom) =
      𝟙 (Over.mk σ.hom) := sorry

/-- The induced morphism of algebraic spaces over `B` preserves composition. -/
theorem SchemeOver.toOver_comp {σ τ υ : SchemeOver B} (f : σ ⟶ τ) (g : τ ⟶ υ) :
    (Over.homMk ((ofOverFunctor S).map (f ≫ g).left) (CostructuredArrow.w (f ≫ g)) :
      Over.mk σ.hom ⟶ Over.mk υ.hom) =
      (Over.homMk ((ofOverFunctor S).map f.left) (CostructuredArrow.w f) :
        Over.mk σ.hom ⟶ Over.mk τ.hom) ≫
        (Over.homMk ((ofOverFunctor S).map g.left) (CostructuredArrow.w g) :
          Over.mk τ.hom ⟶ Over.mk υ.hom) := sorry

/-- The functor sending a scheme over `B` to the associated algebraic space over `B`. -/
def SchemeOver.toOver : SchemeOver B ⥤ Over B where
  obj σ := Over.mk σ.hom
  map f := Over.homMk ((ofOverFunctor S).map f.left) (CostructuredArrow.w f)
  map_id := SchemeOver.toOver_id
  map_comp := SchemeOver.toOver_comp

/-- The object map of `SchemeOver.toOver` is `Over.mk` of the structural morphism. -/
theorem SchemeOver.toOver_obj (σ : SchemeOver B) :
    SchemeOver.toOver.obj σ = Over.mk σ.hom :=
  rfl

/-- The morphism map of `SchemeOver.toOver` is `Over.homMk` of the induced map of
algebraic spaces. -/
theorem SchemeOver.toOver_map {σ τ : SchemeOver B} (f : σ ⟶ τ) :
    SchemeOver.toOver.map f =
      Over.homMk ((ofOverFunctor S).map f.left) (CostructuredArrow.w f) :=
  rfl

/-- The functor on `(Sch/B)ᵒᵖ` represented by a morphism of algebraic spaces `π : X ⟶ B`. -/
def yonedaOver {X : AlgebraicSpace S} (π : X ⟶ B) :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) :=
  SchemeOver.toOver.op ⋙ yoneda.obj (Over.mk π)

/-- Evaluating `yonedaOver π` at a scheme over `B` yields morphisms over `B`. -/
theorem yonedaOver_obj {X : AlgebraicSpace S} (π : X ⟶ B) (σ : SchemeOver B) :
    (yonedaOver π).obj (op σ) = (Over.mk σ.hom ⟶ Over.mk π) :=
  rfl

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space affine of finite
presentation over `B`. -/
def IsAffineFinitePresentationOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
    Affine π ∧ FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space affine of finite presentation over `B` is
existence of a morphism `π` that is affine and of finite presentation together with an
isomorphism to `yonedaOver π`. -/
theorem isAffineFinitePresentationOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsAffineFinitePresentationOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        Affine π ∧ FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  Iff.rfl

/-- Package an affine finite-presentation morphism over `B` and a representing isomorphism
as `IsAffineFinitePresentationOver`. -/
theorem IsAffineFinitePresentationOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    (hAffine : Affine π) (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) : IsAffineFinitePresentationOver F :=
  ⟨X, π, hAffine, hFP, ⟨e⟩⟩

/-- `IsAffineFinitePresentationOver.of` records affinity, finite presentation, and the
given representing isomorphism. -/
theorem IsAffineFinitePresentationOver.of_spec {X : AlgebraicSpace S} {π : X ⟶ B}
    (hAffine : Affine π) (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) :
    Affine π ∧ FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  ⟨hAffine, hFP, ⟨e⟩⟩

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space affine over `B`. -/
def IsAffineOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Affine π ∧ Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space affine over `B` is existence of an
affine morphism `π` together with an isomorphism to `yonedaOver π`. -/
theorem isAffineOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsAffineOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Affine π ∧ Nonempty (F ≅ yonedaOver π) :=
  Iff.rfl

/-- A functor is affine over `B` if it is isomorphic to the relative functor of
points of an affine morphism to `B`. -/
theorem IsAffineOver.of {X : AlgebraicSpace S} {π : X ⟶ B} (hAffine : Affine π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) : IsAffineOver F :=
  ⟨X, π, hAffine, ⟨e⟩⟩

/-- An affine representing morphism has affinity and a natural isomorphism with
the represented functor. -/
theorem IsAffineOver.of_spec {X : AlgebraicSpace S} {π : X ⟶ B} (hAffine : Affine π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    Affine π ∧ Nonempty (F ≅ yonedaOver π) :=
  ⟨hAffine, ⟨e⟩⟩

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space of finite
presentation over `B`. -/
def IsFinitePresentationOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
    FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space of finite presentation over `B` is
existence of a finite presentation morphism `π` together with an isomorphism
to `yonedaOver π`. -/
theorem isFinitePresentationOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsFinitePresentationOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  Iff.rfl

/-- A functor is of finite presentation over `B` if it is isomorphic to the
relative functor of points of a finite-presentation morphism to `B`. -/
theorem IsFinitePresentationOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) : IsFinitePresentationOver F :=
  ⟨X, π, hFP, ⟨e⟩⟩

/-- A finite-presentation representing morphism has finite presentation and a
natural isomorphism with the represented functor. -/
theorem IsFinitePresentationOver.of_spec {X : AlgebraicSpace S} {π : X ⟶ B}
    (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) :
    FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  ⟨hFP, ⟨e⟩⟩

/-- Representability by an algebraic space affine of finite presentation over `B`
is the conjunction of affinity over `B` and finite presentation over `B`. -/
theorem isAffineFinitePresentationOver_iff_affine_and_finitePresentation
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsAffineFinitePresentationOver F ↔ IsAffineOver F ∧ IsFinitePresentationOver F := sorry

end AlgebraicGeometry.AlgebraicSpace
