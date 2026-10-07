module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleCech

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- The ringed space on `X` whose structure sheaf is the inverse image of the structure sheaf
along `f`. Its modules are coefficient modules whose maps need only be linear over the base. -/
abbrev relativeSpace {Y : RingedSpace.{u}} (f : X.toRingedSpace ⟶ Y) : RingedSpace.{u} :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf).toRingedSpace

/-- The canonical morphism from the inverse-image coefficient ringed space to the base ringed
space. -/
noncomputable def relativeSpaceMap {Y : RingedSpace.{u}} (f : X.toRingedSpace ⟶ Y) :
    relativeSpace f ⟶ Y :=
  InducedCategory.homMk
    { base := f.hom.base
      c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf).hom }

/-- The canonical morphism from the inverse-image coefficient ringed space has the same
underlying continuous map as the original morphism. -/
theorem relativeSpaceMap_base {Y : RingedSpace.{u}} (f : X.toRingedSpace ⟶ Y) :
    (relativeSpaceMap f).hom.base = f.hom.base := sorry

end AlgebraicGeometry.Scheme.ModuleCech
