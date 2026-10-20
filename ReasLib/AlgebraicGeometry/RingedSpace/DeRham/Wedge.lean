/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.Wedge
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham

/-!
# Wedge multiplication on relative de Rham complexes of ringed spaces

The wedge product on a ringed site specializes along the inverse-image structure map of a
morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham

variable {X S : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- The canonical wedge morphism on the relative de Rham complex of a ringed-space morphism. -/
noncomputable abbrev wedge (f : X ⟶ S) :
    HomologicalComplex.tensorObj (complex f) (complex f) ⟶ complex f :=
  SheafOfModules.RingedSite.DeRham.wedge (structureMap f)

/-- The homogeneous component of the ringed-space wedge is the canonical exterior product. -/
theorem wedge_component (f : X ⟶ S) (p q : ℕ) :
    HomologicalComplex.Monoidal.tensorHomComponent (wedge f) p q =
      SheafOfModules.RingedSite.DeRham.wedgeComponent (structureMap f) p q := sorry

end AlgebraicGeometry.RingedSpace.DeRham
