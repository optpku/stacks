/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- Direct image along a finite morphism commutes with inverse image in a cartesian
square of schemes for set-valued small étale sheaves. -/
theorem setMap_isIso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsFinite f] :
    IsIso (setMap g f' g' f h_cart.flip F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

namespace AlgebraicGeometry.Scheme.Hom

/-- Torsion abelian étale cohomology commutes with arbitrary base change
in every degree for a finite morphism of schemes. -/
theorem cohomologyCommutesWithBaseChange_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Z : Scheme.{u},
      HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})] :
    CohomologyCommutesWithBaseChange f := sorry

end AlgebraicGeometry.Scheme.Hom
