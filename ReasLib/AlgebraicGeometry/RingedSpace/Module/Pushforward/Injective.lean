module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.CategoryTheory.Adjunction.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat pushforward preserves injective module sheaves

The exact flat pullback is left adjoint to module pushforward, so the latter preserves injective
objects.  The functor-level instance is the owner; the objectwise theorem is its direct interface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.IsFlat

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- Pushforward along a flat morphism of ringed spaces preserves injective module sheaves. -/
@[stacks 02N5 "flat pushforward preserves injectives"]
instance pushforwardPreservesInjectives [RingedSpace.Hom.IsFlat f] :
    (f _*).PreservesInjectiveObjects := sorry

/-- The pushforward of an injective module sheaf along a flat morphism is injective. -/
@[stacks 02N5 "flat pushforward of an injective module"]
theorem injective_pushforward [RingedSpace.Hom.IsFlat f]
    {I : X.Modules} [Injective I] :
    Injective ((f _*).obj I) := sorry

end AlgebraicGeometry.RingedSpace.Hom.IsFlat
