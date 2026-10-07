module

public import stacks_project.Chap99.Lemma_99_3_8_Yoneda

/-!
# Representability by algebraic spaces affine or of finite presentation over a base

A functor on `(Sch/B)ᵒᵖ` is an algebraic space affine over `B` when it is
isomorphic to `yonedaOver π` for an affine morphism `π : X ⟶ B`. Finite
presentation over `B` is the analogous condition with `FinitePresentation π`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space affine over `B`. -/
def IsAffineOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Affine π ∧ Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space affine over `B` is existence of an
affine morphism `π` together with an isomorphism to `yonedaOver π`. -/
theorem isAffineOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsAffineOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Affine π ∧ Nonempty (F ≅ yonedaOver π) :=
  Iff.rfl

/-- Package an affine morphism over `B` and a representing isomorphism as `IsAffineOver`. -/
theorem IsAffineOver.of {X : AlgebraicSpace S} {π : X ⟶ B} (hAffine : Affine π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) : IsAffineOver F :=
  ⟨X, π, hAffine, ⟨e⟩⟩

/-- `IsAffineOver.of` records affinity and the given representing isomorphism. -/
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

/-- Package a finite presentation morphism over `B` and a representing isomorphism
as `IsFinitePresentationOver`. -/
theorem IsFinitePresentationOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) : IsFinitePresentationOver F :=
  ⟨X, π, hFP, ⟨e⟩⟩

/-- `IsFinitePresentationOver.of` records finite presentation and the given
representing isomorphism. -/
theorem IsFinitePresentationOver.of_spec {X : AlgebraicSpace S} {π : X ⟶ B}
    (hFP : FinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) :
    FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  ⟨hFP, ⟨e⟩⟩

/-- Representability by an algebraic space affine of finite presentation over `B`
is the conjunction of affinity over `B` and finite presentation over `B`. -/
theorem isAffineFinitePresentationOver_iff_affine_and_finitePresentation
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsAffineFinitePresentationOver F ↔ IsAffineOver F ∧ IsFinitePresentationOver F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
