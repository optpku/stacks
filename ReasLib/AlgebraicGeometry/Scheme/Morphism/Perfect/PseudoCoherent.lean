module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Perfect and pseudo-coherent morphisms of schemes

A scheme morphism that is locally perfect on affine coordinate rings is pseudo-coherent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- A scheme morphism locally given by perfect ring maps is pseudo-coherent. -/
@[instance]
theorem pseudoCoherent_of_isPerfectRingMap
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfType RingHom.IsPerfectRingMap f] :
    PseudoCoherent f := sorry

end AlgebraicGeometry.LocallyOfType
