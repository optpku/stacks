module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.FinitePresentation
public import ReasLib.RingTheory.RingHom.Perfect.Flat

/-!
# Flat perfect morphisms of schemes

For flat scheme morphisms, being locally perfect on affine coordinate rings is equivalent to
being locally of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace LocallyOfType

/-- A flat, locally finitely presented scheme morphism is locally given by perfect ring maps. -/
@[instance]
theorem isPerfect_of_flat_of_locallyOfFinitePresentation
    {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f] :
    LocallyOfType RingHom.IsPerfectRingMap f := sorry

end LocallyOfType

/-- A scheme morphism is flat and locally perfect exactly when it is flat and locally of finite
presentation. -/
theorem flat_and_perfect_iff_flat_and_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (Flat f ∧ LocallyOfType RingHom.IsPerfectRingMap f) ↔
      (Flat f ∧ LocallyOfFinitePresentation f) := sorry

end AlgebraicGeometry
