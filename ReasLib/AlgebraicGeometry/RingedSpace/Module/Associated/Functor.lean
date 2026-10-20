/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves associated to modules over global scalars

For `alpha : R →+* Γ(X, O_X)`, the associated-module functor is pullback from the ringed point
classified by `alpha`. This file owns the canonical functor and its objects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- The morphism `X ⟶ RingedPoint.of R` classified by
`alpha : R →+* Γ(X, O_X)`. -/
noncomputable abbrev pointMap (alpha : R →+* X.globalSectionsRing) :
    X ⟶ RingedPoint.of R :=
  RingedPoint.fromGlobalSections alpha

/-- The functor sending an `R`-module to its associated `O_X`-module. -/
@[stacks 01BH "associated module functor"]
noncomputable def functor (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.{u} R ⥤ X.Modules :=
  RingedPoint.Module.functor R ⋙ RingedSpace.Hom.pullback (pointMap alpha)

/-- The `O_X`-module associated to `M` through `alpha`. -/
@[stacks 01BI, stacks 01BH "associated module sheaf"]
noncomputable abbrev obj (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) :
    X.Modules :=
  (functor alpha).obj M

end AlgebraicGeometry.RingedSpace.Module.Associated
