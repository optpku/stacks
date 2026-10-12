/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsSupportedInOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.2.2: For an abelian étale sheaf and a locally closed subscheme,
two containing Zariski opens on which the subscheme is closed have canonically
equivalent supported sections. For nested opens, this comparison is restriction. -/
@[stacks 0F6G] #check
  (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionsSupportedInOpenAddEquiv :
    ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      {Z : Scheme.{u}} (ι : Z ⟶ X) (U U' : X.Opens)
      (hU : Set.range ι ⊆ U) (hU' : Set.range ι ⊆ U') [IsImmersion ι]
      [IsClosedImmersion (liftToOpen ι U hU)]
      [IsClosedImmersion (liftToOpen ι U' hU')],
      abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) ≃+
        abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU')))
