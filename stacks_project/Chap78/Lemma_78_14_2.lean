/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Generators
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 78.14.2: if the source and target of a groupoid in algebraic spaces over `B`
are flat, there is a small family of objects of `QCoh(U, R, s, t, c)` such that every
object is the directed colimit of its submodules isomorphic to a family member. -/
@[stacks 0780] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.exists_set_generators :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left],
      ∃ (T : Type u) (family : T → G.QCoh), ∀ A : G.QCoh,
        (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.isoToFamilySubobjects G family A).Nonempty ∧
          DirectedOn (· ≤ ·)
            (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.isoToFamilySubobjects G family A) ∧
            Nonempty (CategoryTheory.Limits.IsColimit
              (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.isoToFamilyCocone G family A)))

