module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Representability

/-!
# Relative representability by algebraic spaces

Typed compatibility checks for the relative representability predicates and their API.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpaceOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isAlgebraicSpaceOver_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    IsAlgebraicSpaceOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpaceOver.of :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X : AlgebraicSpace S} {π : X ⟶ B}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π),
    IsAlgebraicSpaceOver F)

#check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpaceOver.of_spec :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X : AlgebraicSpace S} {π : X ⟶ B}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π),
    Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsLocallyOfFinitePresentationOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isLocallyOfFinitePresentationOver_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    IsLocallyOfFinitePresentationOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        LocallyOfFinitePresentation π ∧ Nonempty (F ≅ yonedaOver π))

#check (AlgebraicGeometry.AlgebraicSpace.IsLocallyOfFinitePresentationOver.of :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X : AlgebraicSpace S} {π : X ⟶ B}
    (hLFP : LocallyOfFinitePresentation π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π),
    IsLocallyOfFinitePresentationOver F)

#check (AlgebraicGeometry.AlgebraicSpace.IsLocallyOfFinitePresentationOver.of_spec :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X : AlgebraicSpace S}
    {π : X ⟶ B} (hLFP : LocallyOfFinitePresentation π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π),
    LocallyOfFinitePresentation π ∧ Nonempty (F ≅ yonedaOver π))
