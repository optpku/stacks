module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Finite type morphisms from relative very ampleness

This file records the finite-type consequence of a quasi-compact relative
projective-bundle immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- A quasi-compact morphism carrying a relatively very ample module is of finite type. -/
theorem RelativelyVeryAmple.finiteType_of_quasiCompact
    [QuasiCompact f] (h : RelativelyVeryAmple f L) :
    Scheme.Hom.FiniteType f := sorry

end AlgebraicGeometry
