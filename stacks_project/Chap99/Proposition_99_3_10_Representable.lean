module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over

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

/- Relative representability predicates and their comparison API. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsAffineOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, ((SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isAffineOver_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    IsAffineOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Affine π ∧ Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsAffineOver.of :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} {π : X ⟶ B} (hAffine : Affine π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π), IsAffineOver F)

#check (AlgebraicGeometry.AlgebraicSpace.IsAffineOver.of_spec :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} {π : X ⟶ B} (hAffine : Affine π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π),
    Affine π ∧ Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsFinitePresentationOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, ((SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isFinitePresentationOver_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    IsFinitePresentationOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsFinitePresentationOver.of :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} {π : X ⟶ B} (hFP : FinitePresentation π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π),
    IsFinitePresentationOver F)

#check (AlgebraicGeometry.AlgebraicSpace.IsFinitePresentationOver.of_spec :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} {π : X ⟶ B} (hFP : FinitePresentation π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π),
    FinitePresentation π ∧ Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.isAffineFinitePresentationOver_iff_affine_and_finitePresentation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    IsAffineFinitePresentationOver F ↔ IsAffineOver F ∧ IsFinitePresentationOver F)
