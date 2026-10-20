module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The pushforward of the structure sheaf of a closed subscheme of standard projective
space, viewed as a module on the ambient projective space. -/
noncomputable abbrev pushforwardStructureSheaf
    (k : Type u) [Field k] (n : ℕ) (C : (scheme k n).IdealSheafData) :
    (scheme k n).Modules :=
  (Scheme.Modules.pushforward C.subschemeι).obj
    (SheafOfModules.unit C.subscheme.ringCatSheaf : C.subscheme.Modules)

/-- The ambient structure-sheaf module is the pushforward of the unit module on the
closed subscheme. -/
theorem pushforwardStructureSheaf_spec
    (k : Type u) [Field k] (n : ℕ) (C : (scheme k n).IdealSheafData) :
    pushforwardStructureSheaf k n C =
      (Scheme.Modules.pushforward C.subschemeι).obj
        (SheafOfModules.unit C.subscheme.ringCatSheaf : C.subscheme.Modules) := rfl

/-- The pushforward of the structure sheaf of a closed subscheme of standard projective
space is coherent. -/
instance instIsCoherent_pushforwardStructureSheaf
    (k : Type u) [Field k] (n : ℕ) (C : (scheme k n).IdealSheafData) :
    (pushforwardStructureSheaf k n C).IsCoherent := sorry

end AlgebraicGeometry.ProjectiveSpace
