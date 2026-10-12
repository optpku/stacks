/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.67.7 (1): restriction identifies flat, separated, locally finite-type and
locally quasi-finite schemes over an admissible pushout with compatible such schemes over
its two components. -/
@[stacks 0ECL] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.flatBaseChangeIsEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j],
      Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.Pushout.baseChange
          ((@AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.IsSeparated ⊓
              @AlgebraicGeometry.LocallyOfFiniteType ⊓
              @AlgebraicGeometry.LocallyQuasiFinite) :
            MorphismProperty AlgebraicGeometry.Scheme.{u}) i.left j.left))

/- Lemma 37.67.7 (2): restriction identifies étale, separated, locally finite-type and
locally quasi-finite schemes over an admissible pushout with compatible such schemes over
its two components. -/
@[stacks 0ECL] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.etaleBaseChangeIsEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j],
      Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.Pushout.baseChange
          ((@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.IsSeparated ⊓
              @AlgebraicGeometry.LocallyOfFiniteType ⊓
              @AlgebraicGeometry.LocallyQuasiFinite) :
            MorphismProperty AlgebraicGeometry.Scheme.{u}) i.left j.left))
