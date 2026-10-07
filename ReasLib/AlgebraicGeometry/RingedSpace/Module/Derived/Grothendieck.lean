module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Grothendieck Module Categories on Ringed Spaces

`RingedSpace.Modules X` is definitionally a sheaf-of-modules category.  Its
Grothendieck-abelian instance is therefore owned by the generic
`SheafOfModules` leaf.  This module retains named ringed-space bridge theorems.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

namespace Modules

/-- The module category of a ringed space is Grothendieck abelian.
The canonical instance is `SheafOfModules.isGrothendieckAbelian`; this theorem is a
ringed-space-facing compatibility bridge, not another instance owner. -/
@[stacks 0142]
theorem isGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} X.Modules := sorry

/-- The module category of a ringed space has enough injectives for right-derived functors.
This is a consequence of its Grothendieck-abelian structure and does not require a choice of
base scheme or base field. -/
instance hasInjectiveResolutions (X : RingedSpace.{u}) :
    HasInjectiveResolutions X.Modules := sorry

end Modules

end AlgebraicGeometry.RingedSpace
