module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Representation of generic-point freeness

Representability and geometric properties of the functor recording freeness at the generic
points of fibres.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Flattening
namespace freeAtGenericPointsFunctor

/-- For every rank, the generic-point freeness functor of a finite-type quasicoherent module is
represented by a scheme immersed in the base. -/
theorem existsImmersionRepresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [GeometricallyIrreducible f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (p : ℕ) :
    ∃ Sₚ : Over S,
      Nonempty ((freeAtGenericPointsFunctor f ℱ p).RepresentableBy Sₚ) ∧
        IsImmersion Sₚ.hom := sorry

/-- The generic-point freeness functor of a finite-type quasicoherent module is representable. -/
instance instIsRepresentable {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [GeometricallyIrreducible f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (p : ℕ) :
    (freeAtGenericPointsFunctor f ℱ p).IsRepresentable := sorry

/-- The canonical representing scheme of the generic-point freeness functor is immersed in the
base scheme. -/
instance instIsImmersionReprX {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [GeometricallyIrreducible f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (p : ℕ) :
    IsImmersion (Functor.reprX (freeAtGenericPointsFunctor f ℱ p)).hom := sorry

/-- For every rank, the generic-point freeness functor of a finitely presented module has an
immersed representing scheme that is finitely presented over the base. -/
theorem existsImmersionRepresentationOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyIrreducible f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] (p : ℕ) :
    ∃ Sₚ : Over S,
      Nonempty ((freeAtGenericPointsFunctor f ℱ p).RepresentableBy Sₚ) ∧
        IsImmersion Sₚ.hom ∧ Scheme.Hom.FinitePresentation Sₚ.hom := sorry

/-- For a finitely presented module, the canonical representing scheme of the generic-point
freeness functor is finitely presented over the base. -/
instance instFinitePresentationReprX {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [GeometricallyIrreducible f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] (p : ℕ) :
    Scheme.Hom.FinitePresentation
      (Functor.reprX (freeAtGenericPointsFunctor f ℱ p)).hom := sorry

end freeAtGenericPointsFunctor
end Flattening
end Scheme
end AlgebraicGeometry
