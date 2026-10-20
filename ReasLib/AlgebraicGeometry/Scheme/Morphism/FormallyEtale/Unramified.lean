module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/-- An unramified flat morphism of schemes is formally étale. -/
instance toFormallyEtale {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] [Flat f] :
    FormallyEtale f := sorry

end AlgebraicGeometry.Unramified
