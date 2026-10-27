/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReducedConnected.Genus

/-!
# Open restrictions and fixed-genus loci of geometrically reduced connected curves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseOpen :
    ∀ {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens), Over S)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseOpenι :
    ∀ {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens),
      baseOpen P U ⟶ base P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseChangeToOpen :
    ∀ {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens), Obj S)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseOpen_hom :
    ∀ {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens),
    (baseOpen P U).hom = U.ι ≫ (base P).hom)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseOpenι_left :
    ∀ {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens),
    (baseOpenι P U).left = U.ι)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseChangeToOpen_hom :
    ∀ {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens),
    hom (baseChangeToOpen P U) =
      pullback.snd (hom P) (ofOverMap (baseOpenι P U)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.baseChangeToOpen_base :
    ∀ {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens),
    base (baseChangeToOpen P U) = baseOpen P U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1OfGenus :
    ∀ (g : ℕ) (S : Scheme.{u}), CategoryTheory.ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1OfGenus_iff :
    ∀ (g : ℕ) {S : Scheme.{u}}
    (P : Obj S),
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      geometricallyReducedConnectedDim1 S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1OfGenus_iff_ofGenus :
    ∀ (g : ℕ)
    {S : Scheme.{u}} (P : Obj S),
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      geometricallyReducedConnectedDim1 S P ∧ ofGenus g S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.eq_of_mem_geometricallyReducedConnectedDim1OfGenus :
    ∀ {S : Scheme.{u}} {P : Obj S} {g g' : ℕ} (hpt : Nonempty (base P).left)
    (hg : geometricallyReducedConnectedDim1OfGenus g S P)
    (hg' : geometricallyReducedConnectedDim1OfGenus g' S P),
    g = g')

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
