/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.toOver :
    SchemeOver B ⥤ Over B)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.toOver_obj :
    ∀ (σ : SchemeOver B),
      SchemeOver.toOver.obj σ = Over.mk σ.hom)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.toOver_map :
    ∀ {σ τ : SchemeOver B} (f : σ ⟶ τ),
      SchemeOver.toOver.map f =
      Over.homMk ((ofOverFunctor S).map f.left) (CostructuredArrow.w f))

#check (AlgebraicGeometry.AlgebraicSpace.yonedaOver :
    ∀ {X : AlgebraicSpace S} (π : X ⟶ B),
      (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.yonedaOver_obj :
    ∀ {X : AlgebraicSpace S} (π : X ⟶ B) (σ : SchemeOver B),
      (yonedaOver π).obj (op σ) = (Over.mk σ.hom ⟶ Over.mk π))

#check (AlgebraicGeometry.AlgebraicSpace.IsAffineFinitePresentationOver :
    ∀ (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
      Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isAffineFinitePresentationOver_iff :
    ∀ (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
      IsAffineFinitePresentationOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        Affine π ∧ FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsAffineFinitePresentationOver.of :
    ∀ {X : AlgebraicSpace S} {π : X ⟶ B}
    (hAffine : Affine π) (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π),
      IsAffineFinitePresentationOver F)

#check (AlgebraicGeometry.AlgebraicSpace.IsAffineFinitePresentationOver.of_spec :
    ∀ {X : AlgebraicSpace S} {π : X ⟶ B}
    (hAffine : Affine π) (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π),
      Affine π ∧ FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π))

end AlgebraicGeometry.AlgebraicSpace
