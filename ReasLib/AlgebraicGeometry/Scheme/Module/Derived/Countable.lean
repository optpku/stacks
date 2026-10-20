/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Countable
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver.Countable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Category
public import ReasLib.CategoryTheory.DerivedCategory.Countable
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The bounded derived category with coherent cohomology on a finite-type scheme over a
countable Noetherian ring has a countable skeleton. -/
instance countableCategory_boundedCoherent
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X : Scheme.FiniteTypeOver (Spec (CommRingCat.of R))) :
    CountableCategory
      (Skeleton
        (DerivedCategory.Bounded.CohomologyIn
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))) := sorry

/-- The perfect derived category of a finite-type scheme over a countable Noetherian ring has a
countable skeleton. -/
instance countableCategory_perfect
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X : Scheme.FiniteTypeOver (Spec (CommRingCat.of R))) :
    CountableCategory
      (Skeleton
        (@ModuleDerived.Perfect (Over.left X.obj).toRingedSpace)) := sorry

end AlgebraicGeometry.Scheme
