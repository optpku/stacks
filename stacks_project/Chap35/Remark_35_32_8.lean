module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.SurjectiveSquare.Counterexamples
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 35.32.8 (1): a property of scheme morphisms is étale local in surjective
squares if it has the same truth value on the horizontal maps of every commutative
square whose vertical maps are surjective and étale. -/
@[stacks 04R4]
#check (AlgebraicGeometry.IsEtaleLocalInSurjectiveSquares :
  MorphismProperty Scheme.{u} → Prop)

/- Remark 35.32.8 (2): étale locality on source-and-target implies invariance in
commutative squares with surjective étale vertical maps. -/
@[stacks 04R4]
#check (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.toIsEtaleLocalInSurjectiveSquares :
  ∀ (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P],
    IsEtaleLocalInSurjectiveSquares P)

/- Remark 35.32.8 (3): for a property compatible with étale restriction,
coproducts, and empty-source open immersions, invariance in surjective étale
squares implies étale locality on the source. -/
@[stacks 04R4]
#check (AlgebraicGeometry.IsEtaleLocalInSurjectiveSquares.toIsLocalAtSource :
  ∀ (P : MorphismProperty Scheme.{u}) [IsEtaleLocalInSurjectiveSquares P]
    [P.RespectsLeft (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderCoproducts.{u}]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})],
    P.IsLocalAtSource Scheme.etalePrecoverage)

/- Remark 35.32.8 (4): for a property compatible with étale base change and
coproducts, invariance in surjective étale squares implies étale locality on
the target. -/
@[stacks 04R4]
#check (AlgebraicGeometry.IsEtaleLocalInSurjectiveSquares.toIsLocalAtTarget :
  ∀ (P : MorphismProperty Scheme.{u}) [IsEtaleLocalInSurjectiveSquares P]
    [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderCoproducts.{u}],
    P.IsLocalAtTarget Scheme.etalePrecoverage)

/- Remark 35.32.8 (5): having locally Noetherian target is invariant in commutative
squares with surjective étale vertical maps. -/
@[stacks 04R4]
#check (AlgebraicGeometry.LocallyNoetherianTarget.isEtaleLocalInSurjectiveSquares :
  IsEtaleLocalInSurjectiveSquares
    (LocallyNoetherianTarget : MorphismProperty Scheme.{u}))

/- Remark 35.32.8 (6): invariance in surjective étale squares does not imply étale
locality on source-and-target, as witnessed by `LocallyNoetherianTarget`. -/
@[stacks 04R4]
#check (AlgebraicGeometry.LocallyNoetherianTarget.notIsEtaleLocalAtSourceAndTarget :
  ¬ IsEtaleLocalAtSourceAndTarget
    (LocallyNoetherianTarget : MorphismProperty Scheme.{0}))

/- Remark 35.32.8 (7): separate étale locality on the source and target does not imply
invariance in surjective étale squares, as witnessed by `NoetherianAtSpecializations`. -/
@[stacks 04R4]
#check (AlgebraicGeometry.NoetherianAtSpecializations.notIsEtaleLocalInSurjectiveSquares :
  ¬ IsEtaleLocalInSurjectiveSquares
    (NoetherianAtSpecializations : MorphismProperty Scheme.{0}))

/- Remark 35.32.8 (8): for a property compatible with étale restriction, étale
base change, and coproducts, stability under postcomposition with open immersions
makes invariance in surjective étale squares equivalent to étale locality on
source-and-target. -/
@[stacks 04R4]
#check (AlgebraicGeometry.IsEtaleLocalInSurjectiveSquares.iff_sourceAndTarget_of_respectsRightOpenImmersion :
  ∀ (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})]
    [P.IsStableUnderCoproducts.{u}]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})],
    IsEtaleLocalInSurjectiveSquares P ↔ IsEtaleLocalAtSourceAndTarget P)
