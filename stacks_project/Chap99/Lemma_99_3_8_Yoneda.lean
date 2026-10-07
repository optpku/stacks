module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Yoneda comparison for algebraic spaces over `B`

Schemes over an algebraic space `B` map to the slice `Over B` of algebraic
spaces, and a morphism `π : X ⟶ B` represents a functor on `(Sch/B)ᵒᵖ` by
morphisms over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The functor sending a scheme over `B` to the associated algebraic space over `B`. -/
def SchemeOver.toOver : SchemeOver B ⥤ Over B where
  obj σ := Over.mk σ.hom
  map f := Over.homMk ((ofOverFunctor S).map f.left) (CostructuredArrow.w f)
  map_id := sorry
  map_comp := sorry

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

end AlgebraicGeometry.AlgebraicSpace
