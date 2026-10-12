/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Cohomology
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 30.4.3 [0BDY]: on a quasi-compact scheme with affine diagonal, every quasicoherent
module embeds into one whose positive-degree global cohomology vanishes. -/
@[stacks 0BDY] #check
  (AlgebraicGeometry.Scheme.QCoh.exists_mono_to_globalCohomologyAcyclic :
    ∀ {X : Scheme.{u}} [CompactSpace X.carrier]
      [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] (F : AlgebraicGeometry.Scheme.QCoh X),
      ∃ (F' : AlgebraicGeometry.Scheme.QCoh X) (i : F ⟶ F'), Mono i ∧
        AlgebraicGeometry.Scheme.QCoh.globalCohomologyAcyclic X F')

#check
  (AlgebraicGeometry.Scheme.QCoh.exists_universal_globalCohomology_deltaFunctor :
    ∀ (X : Scheme.{u}) [CompactSpace X.carrier]
      [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))],
      ∃ T : CohomologicalDeltaFunctor (AlgebraicGeometry.Scheme.QCoh X) AddCommGrpCat,
        (∀ n : ℕ, (T.F n).obj =
          AlgebraicGeometry.Scheme.QCoh.globalCohomologyFunctor X n) ∧ T.IsUniversal)
