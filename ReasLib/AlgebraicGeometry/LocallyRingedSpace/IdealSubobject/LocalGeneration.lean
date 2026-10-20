module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.LocalGeneration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally generated ideals on locally ringed spaces
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- Local generation of an ideal subobject by sections. -/
@[stacks 01HN "locally generated ideal subobject"]
abbrev IdealSubobject.IsLocallyGeneratedBySections
    {X : LocallyRingedSpace.{u}} (I : IdealSubobject X) : Prop :=
  RingedSpace.IdealSubobject.IsLocallyGeneratedBySections I

/-- Local generation at the locally-ringed-space layer is equivalent to the existence of the
underlying local-generator data. -/
@[stacks 01HN "locally-ringed-space ideal local-generator data"]
theorem IdealSubobject.isLocallyGeneratedBySections_iff
    {X : LocallyRingedSpace.{u}} (I : IdealSubobject X) :
    I.IsLocallyGeneratedBySections ↔ Nonempty I.toModule.LocalGeneratorsData.{u} := sorry

end AlgebraicGeometry.LocallyRingedSpace
