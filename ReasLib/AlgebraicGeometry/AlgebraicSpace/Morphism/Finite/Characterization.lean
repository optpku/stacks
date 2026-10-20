module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DiscreteFieldFibers
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Characterizations of finite morphisms of algebraic spaces

A morphism of algebraic spaces is finite if and only if it is proper and
locally quasi-finite, equivalently proper with discrete field fibers, equivalently
universally closed, separated, and locally of finite type with discrete field
fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsFinite

/-- For a morphism of algebraic spaces over a scheme, the following are
equivalent: finiteness; properness and local quasi-finiteness; properness and
discrete field fibers; universal closedness, separation, local finite type,
and discrete field fibers. -/
theorem proper_discreteFieldFibers_tfae {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ IsFinite f
      , Proper f ∧ LocallyQuasiFinite f
      , Proper f ∧ discreteFieldFibers f
      , UniversallyClosed f ∧ Separated f ∧ LocallyOfFiniteType f ∧
          discreteFieldFibers f ] :=
  sorry

/-- A morphism of algebraic spaces is finite if and only if it is proper and
locally quasi-finite. -/
theorem iff_proper_and_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsFinite f ↔ Proper f ∧ LocallyQuasiFinite f :=
  (proper_discreteFieldFibers_tfae f).out 0 1

/-- A morphism of algebraic spaces is finite if and only if it is proper and
has discrete field fibers. -/
theorem iff_proper_and_discreteFieldFibers {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsFinite f ↔ Proper f ∧ discreteFieldFibers f :=
  (proper_discreteFieldFibers_tfae f).out 0 2

/-- A proper and locally quasi-finite morphism of algebraic spaces is finite. -/
@[instance 100]
theorem of_proper_of_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [LocallyQuasiFinite f] :
    IsFinite f :=
  (iff_proper_and_locallyQuasiFinite f).mpr ⟨inferInstance, inferInstance⟩

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
