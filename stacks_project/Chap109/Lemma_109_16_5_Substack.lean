/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0.Genus

/-!
# Smooth curve families of fixed genus

The fixed-genus predicate and its membership, uniqueness, and isomorphism
invariance API are owned by the shared genus-locus module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0OfGenus :
  ℕ → (S : Scheme.{u}) → ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0OfGenus_iff :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    smoothH0OfGenus g S P ↔
      smoothH0 S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0OfGenus_iff_ofGenus :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    smoothH0OfGenus g S P ↔ smoothH0 S P ∧ ofGenus g S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0OfGenus_le_smoothH0 :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    smoothH0OfGenus g S P → smoothH0 S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0OfGenus_le_ofGenus :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    smoothH0OfGenus g S P → ofGenus g S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.eq_of_mem_smoothH0OfGenus :
  ∀ {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : smoothH0OfGenus g S P) (hg' : smoothH0OfGenus g' S P),
    g = g')

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_smoothH0OfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}),
    (smoothH0OfGenus g S).IsClosedUnderIsomorphisms)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
