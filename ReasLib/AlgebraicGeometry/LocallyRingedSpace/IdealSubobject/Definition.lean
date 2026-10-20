module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal subobjects of locally ringed spaces

This foundational leaf only specializes the ringed-space ideal-subobject carrier and its
represented module. Kernel, pullback, and local-generation APIs live in focused submodules.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- An ideal subobject of a locally ringed space. -/
@[stacks 01HN "locally-ringed-space ideal subobject"]
abbrev IdealSubobject (X : LocallyRingedSpace.{u}) : Type (u + 1) :=
  RingedSpace.IdealSubobject X.toRingedSpace

/-- The module sheaf represented by a locally-ringed-space ideal subobject. -/
@[stacks 01HN "ideal subobject module"]
noncomputable abbrev IdealSubobject.toModule
    {X : LocallyRingedSpace.{u}} (I : IdealSubobject X) :
    RingedSpace.Modules X.toRingedSpace :=
  RingedSpace.IdealSubobject.toModule I

end AlgebraicGeometry.LocallyRingedSpace
