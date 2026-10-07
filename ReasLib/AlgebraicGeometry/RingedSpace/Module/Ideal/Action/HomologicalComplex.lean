module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise monic ideal actions on ringed-space complexes

This file fixes the opens site and structure sheaf determined by a ringed space.  It is the
typeclass-facing bridge through which downstream declarations can write
`IdealSheaf.IsActionMono.Complex I K` without rebuilding hidden site parameters.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.RingedSpace.IdealSheaf

variable {X : RingedSpace.{u}} {ι : Type v}

/-- The ideal action on an `X.Modules` object is monomorphic.  This abbreviation fixes the opens
site and structure sheaf supplied by `X`. -/
abbrev IsActionMono
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) : Prop :=
  SheafOfModules.RingedSite.IdealSheaf.IsActionMono (O := X.sheaf) I M

namespace IsActionMono

/-- The object property of complexes of `X.Modules` on which `I` acts monomorphically in every
degree. -/
@[stacks 0F8N "degreewise monic ideal action on a ringed space"]
abbrev complex
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (c : ComplexShape ι) : ObjectProperty (HomologicalComplex X.Modules c) :=
  SheafOfModules.RingedSite.IdealSheaf.IsActionMono.complex
    (J := Opens.grothendieckTopology X) (O := X.sheaf) I c

/-- The typeclass view of degreewise monicity of the `I`-action. -/
@[stacks 0F8N "degreewise ideal-action predicate on a ringed space"]
abbrev Complex
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {c : ComplexShape ι} (K : HomologicalComplex X.Modules c) : Prop :=
  SheafOfModules.RingedSite.IdealSheaf.IsActionMono.Complex
    (J := Opens.grothendieckTopology X) (O := X.sheaf) I K

/-- Complexes with degreewise monic `I`-action, as a full subcategory. -/
abbrev Complexes
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (c : ComplexShape ι) := (complex I c).FullSubcategory

/-- The ringed-space property is equivalent to monicity of the ideal action in every degree. -/
theorem complex_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {c : ComplexShape ι} (K : HomologicalComplex X.Modules c) :
    complex I c K ↔ ∀ i : ι,
      IdealSheaf.IsActionMono I (K.X i) := sorry

/-- The object-property and typeclass views of degreewise monic action agree. -/
theorem complex_iff_complex
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {c : ComplexShape ι} (K : HomologicalComplex X.Modules c) :
    complex I c K ↔ Complex I K := sorry

/-- Every term of a ringed-space complex with degreewise monic ideal action has monic action. -/
instance Complex.term
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {c : ComplexShape ι} (K : HomologicalComplex X.Modules c)
    [Complex I K] (i : ι) :
    IdealSheaf.IsActionMono I (K.X i) := sorry

/-- An object of the full subcategory carries the corresponding typeclass property. -/
instance Complexes.complex
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {c : ComplexShape ι} (K : Complexes I c) : Complex I K.obj := sorry

end IsActionMono

end AlgebraicGeometry.RingedSpace.IdealSheaf
