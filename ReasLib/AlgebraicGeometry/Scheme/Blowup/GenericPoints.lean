module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.GenericPoints

/-!
# Generic points of blowups

A blowup identifies the generic points of its source with the generic points of the base outside
the center.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsBlowup

/-- A blowup morphism bijects the generic points of its source with the generic points of the
base lying outside the support of its center. -/
theorem bijOn_genericPoints_compl_support
    {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    Set.BijOn b
      (genericPoints X')
      (genericPoints X ∩ (I.support : Set X)ᶜ) := sorry

end AlgebraicGeometry.IsBlowup
