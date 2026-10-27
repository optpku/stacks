/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable.Genus

/-!
# The object property of prestable families of a given genus

The fixed-genus prestable locus and its membership, inclusion, and
isomorphism-invariance API are supplied by the shared genus owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestableOfGenus :
  ℕ → (S : Scheme.{u}) → ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestableOfGenus_iff :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    prestableOfGenus g S P ↔ prestable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestableOfGenus_iff_ofGenus :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    prestableOfGenus g S P ↔ prestable S P ∧ ofGenus g S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestableOfGenus_le_prestable :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    prestableOfGenus g S P → prestable S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestableOfGenus_le_ofGenus :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    prestableOfGenus g S P → ofGenus g S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.eq_of_mem_prestableOfGenus :
  ∀ {S : Scheme.{u}} {P : Obj S} {g g' : ℕ},
    Nonempty (base P).left → prestableOfGenus g S P → prestableOfGenus g' S P → g = g')

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_prestableOfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}), (prestableOfGenus g S).IsClosedUnderIsomorphisms)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
