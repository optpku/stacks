module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.FinitePresentation
public import ReasLib.RingTheory.RingHom.Perfect.CompleteIntersection

/-!
# Finiteness of local complete-intersection morphisms

Local complete-intersection morphisms of schemes are perfect, pseudo-coherent, and locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- A local complete-intersection morphism of schemes is perfect. -/
@[instance]
theorem isPerfect_of_isLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    LocallyOfType RingHom.IsPerfectRingMap f := sorry

/-- A local complete-intersection morphism of schemes is pseudo-coherent. -/
@[instance]
theorem pseudoCoherent_of_isLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    PseudoCoherent f := sorry

/-- A local complete-intersection morphism of schemes is locally of finite presentation. -/
@[instance]
theorem locallyOfFinitePresentation_of_isLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    LocallyOfFinitePresentation f := sorry

/-- A local complete-intersection morphism of schemes is locally of finite type. -/
@[instance]
theorem locallyOfFiniteType_of_isLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    LocallyOfFiniteType f := sorry

end AlgebraicGeometry.LocallyOfType
