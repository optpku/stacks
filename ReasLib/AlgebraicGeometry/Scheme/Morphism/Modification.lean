module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Modifications of Integral Schemes

This leaf owns the standard property of a proper birational morphism between
integral schemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X' X : Scheme.{u}}

/-- A modification is a proper birational morphism between integral schemes. -/
class IsModification (f : X' ⟶ X) : Prop extends IsProper f where
  /-- The source of a modification is integral. -/
  isIntegralSource : IsIntegral X'
  /-- The target of a modification is integral. -/
  isIntegralTarget : IsIntegral X
  /-- A modification is birational. -/
  toIsBirational : IsBirational f

attribute [instance] IsModification.isIntegralSource IsModification.isIntegralTarget

/-- A modification supplies birationality to typeclass search. -/
instance instIsBirationalOfIsModification (f : X' ⟶ X) [h : IsModification f] :
    IsBirational f := sorry

/-- Over integral source and target schemes, modifications are exactly proper
birational morphisms. -/
theorem isModification_iff (f : X' ⟶ X) [IsIntegral X'] [IsIntegral X] :
    IsModification f ↔ IsBirational f ∧ IsProper f := sorry

end

end AlgebraicGeometry
