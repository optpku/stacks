/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable.Genus

/-!
# Fixed-genus semistable families

The fixed-genus predicate, membership, inclusion, nonempty-base uniqueness,
and isomorphism invariance are provided by the shared genus-locus API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.semistableOfGenus
    : ℕ → (S : Scheme.{u}) → ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.semistableOfGenus_iff
    : ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    semistableOfGenus g S P ↔
      semistable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.semistableOfGenus_le_semistable
    : ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    semistableOfGenus g S P → semistable S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.eq_of_mem_semistableOfGenus
    : ∀ {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : semistableOfGenus g S P) (hg' : semistableOfGenus g' S P),
    g = g')

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_semistableOfGenus
    : ∀ (g : ℕ) (S : Scheme.{u}),
    (semistableOfGenus g S).IsClosedUnderIsomorphisms)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
