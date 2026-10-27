/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Genus

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- The fixed-genus object property and its canonical companion API. -/
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.ofGenus :
  ℕ → (S : Scheme.{u}) → ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.ofGenus_iff :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    ofGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        (∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1) ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_ofGenus :
  ∀ (g : ℕ) (S : Scheme.{u}), (ofGenus g S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.ofGenus_le_h0Dim1 :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S), ofGenus g S P → h0Dim1 S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.eq_of_mem_ofGenus :
  ∀ {S : Scheme.{u}} {P : Obj S} {g g' : ℕ},
    Nonempty (base P).left → ofGenus g S P → ofGenus g' S P → g = g')

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
