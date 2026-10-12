/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.41.11 (1): a surjective universally closed image of a quasi-separated scheme is
quasi-separated. -/
@[stacks 09MQ] #check
  (AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_surjective_universallyClosed :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyClosed f]
      [QuasiSeparatedSpace X],
      QuasiSeparatedSpace Y)

/- Lemma 29.41.11 (2): a surjective universally closed image of a separated scheme is
separated. -/
@[stacks 09MQ] #check
  (AlgebraicGeometry.Scheme.isSeparated_of_surjective_universallyClosed :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyClosed f]
      [X.IsSeparated],
      Y.IsSeparated)

/- Lemma 29.41.11 (3): relative quasi-separatedness descends through a surjective universally
closed morphism. -/
@[stacks 09MQ] #check
  (AlgebraicGeometry.QuasiSeparated.of_comp_surjective_universallyClosed :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyClosed f]
      [AlgebraicGeometry.QuasiSeparated (f ≫ g)],
      AlgebraicGeometry.QuasiSeparated g)

/- Lemma 29.41.11 (4): relative separatedness descends through a surjective universally closed
morphism. -/
@[stacks 09MQ] #check
  (AlgebraicGeometry.IsSeparated.of_comp_surjective_universallyClosed :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyClosed f]
      [AlgebraicGeometry.IsSeparated (f ≫ g)],
      AlgebraicGeometry.IsSeparated g)
