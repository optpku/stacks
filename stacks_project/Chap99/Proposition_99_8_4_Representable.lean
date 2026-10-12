/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap99.Lemma_99_3_8_Yoneda

/-!
# Representability by algebraic spaces over a base

A functor on `(Sch/B)ᵒᵖ` is an algebraic space over `B` when it is isomorphic
to `yonedaOver π` for a morphism `π : X ⟶ B` of algebraic spaces. Locally of
finite presentation over `B` is the analogous condition with
`LocallyOfFinitePresentation π`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space over `B`. -/
def IsAlgebraicSpaceOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space over `B` is existence of a morphism
`π` together with an isomorphism to `yonedaOver π`. -/
theorem isAlgebraicSpaceOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsAlgebraicSpaceOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Nonempty (F ≅ yonedaOver π) :=
  Iff.rfl

/-- Package a morphism over `B` and a representing isomorphism as
`IsAlgebraicSpaceOver`. -/
theorem IsAlgebraicSpaceOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    IsAlgebraicSpaceOver F :=
  ⟨X, π, ⟨e⟩⟩

/-- `IsAlgebraicSpaceOver.of` records the given representing isomorphism. -/
theorem IsAlgebraicSpaceOver.of_spec {X : AlgebraicSpace S} {π : X ⟶ B}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    Nonempty (F ≅ yonedaOver π) :=
  ⟨e⟩

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space locally of
finite presentation over `B`. -/
def IsLocallyOfFinitePresentationOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
    LocallyOfFinitePresentation π ∧ Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space locally of finite presentation over
`B` is existence of a locally of finite presentation morphism `π` together with
an isomorphism to `yonedaOver π`. -/
theorem isLocallyOfFinitePresentationOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsLocallyOfFinitePresentationOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        LocallyOfFinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  Iff.rfl

/-- Package a locally of finite presentation morphism over `B` and a
representing isomorphism as `IsLocallyOfFinitePresentationOver`. -/
theorem IsLocallyOfFinitePresentationOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    (hLFP : LocallyOfFinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) : IsLocallyOfFinitePresentationOver F :=
  ⟨X, π, hLFP, ⟨e⟩⟩

/-- `IsLocallyOfFinitePresentationOver.of` records locally of finite presentation
and the given representing isomorphism. -/
theorem IsLocallyOfFinitePresentationOver.of_spec {X : AlgebraicSpace S}
    {π : X ⟶ B} (hLFP : LocallyOfFinitePresentation π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    LocallyOfFinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  ⟨hLFP, ⟨e⟩⟩

end AlgebraicGeometry.AlgebraicSpace
