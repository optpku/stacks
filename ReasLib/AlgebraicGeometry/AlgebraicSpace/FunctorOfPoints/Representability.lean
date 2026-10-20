/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over

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

/-- A functor is represented by an algebraic space over `B` if it is isomorphic
to the relative functor of points of a morphism to `B`. -/
theorem IsAlgebraicSpaceOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    IsAlgebraicSpaceOver F :=
  ⟨X, π, ⟨e⟩⟩

/-- An isomorphism to a relative functor of points witnesses the existence of
a representing isomorphism. -/
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

/-- A functor is represented by an algebraic space locally of finite presentation
over `B` if it is isomorphic to the relative functor of points of such a morphism. -/
theorem IsLocallyOfFinitePresentationOver.of {X : AlgebraicSpace S} {π : X ⟶ B}
    (hLFP : LocallyOfFinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) : IsLocallyOfFinitePresentationOver F :=
  ⟨X, π, hLFP, ⟨e⟩⟩

/-- A locally finitely presented morphism and an isomorphism to its relative
functor of points give local finite presentation and a representing isomorphism. -/
theorem IsLocallyOfFinitePresentationOver.of_spec {X : AlgebraicSpace S}
    {π : X ⟶ B} (hLFP : LocallyOfFinitePresentation π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    LocallyOfFinitePresentation π ∧ Nonempty (F ≅ yonedaOver π) :=
  ⟨hLFP, ⟨e⟩⟩

end AlgebraicGeometry.AlgebraicSpace
