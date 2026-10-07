module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Definition 36.35.1: for a flat, locally finitely presented morphism `f : X ⟶ S`, a
derived `𝒪_X`-module is perfect relative to `S` when it is pseudo-coherent over `𝒪_X` and
locally has finite Tor dimension after restriction to `f⁻¹𝒪_S`. -/
@[stacks 0DI0] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo :
    {X S : Scheme.{u}} → (f : X ⟶ S) → [Flat f] → [LocallyOfFinitePresentation f] →
      RingedSpace.ModuleDerived X.toRingedSpace → Prop)
