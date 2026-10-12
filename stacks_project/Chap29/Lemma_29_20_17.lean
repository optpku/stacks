/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.20.17 (1): finite-type quasi-finiteness at a point descends from a composite to its
left factor. -/
@[stacks 03WR] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt.of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X),
      AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt (f ≫ g) x →
        AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- Lemma 29.20.17 (2): local finite type together with local quasi-finiteness descends from a
composite to its left factor. -/
@[stacks 03WR] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S),
      (AlgebraicGeometry.LocallyOfFiniteType (f ≫ g) ∧
          AlgebraicGeometry.LocallyQuasiFinite (f ≫ g)) →
        AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.LocallyQuasiFinite f)
