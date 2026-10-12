/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProperCharacteristicP
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 59.63.5 (1): constant ZMod p étale cohomology of a proper scheme
over an algebraically closed field of characteristic p > 0 is finite in every degree. -/
@[stacks 0A3P] #check
  (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomology_finite_of_isProper :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p]
      [Fact (0 < p)] (X : SchemeOverField k) [IsProper X.hom]
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
      (q : ℕ), Finite (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomology X.left p q))

/- Lemma 59.63.5 (2): canonical pullback along an algebraically closed field extension
is an isomorphism on constant ZMod p étale cohomology of a proper scheme. -/
@[stacks 0A3P] #check
  (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomologyPullback_isIso_of_isProper :
    ∀ {k k' : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p]
      [Fact (0 < p)] (X : SchemeOverField k) [IsProper X.hom]
      [Field k'] [IsAlgClosed k'] [Algebra k k']
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [HasSheafify (FieldExtension.Over.baseChange k k' X).left.smallEtaleTopology
        AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (FieldExtension.Over.baseChange k k' X).left.smallEtaleTopology
        AddCommGrpCat.{u + 1})]
      (q : ℕ), IsIso (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomologyPullback
        (FieldExtension.Over.toSource k k' X) p q))

end
