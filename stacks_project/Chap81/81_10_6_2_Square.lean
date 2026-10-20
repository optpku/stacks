/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Square

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

universe u

/- The open-complement square commutes. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.square_comm :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i], restrictF f i ≫ j i = j' f i ≫ f)

/- Its overlap is isomorphic to the complement of the inverse-image closed subspace. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.V_isComplement :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i],
    IsIsomorphic (V f i) (closedImmersionComplement (inverseImageι f i)))
