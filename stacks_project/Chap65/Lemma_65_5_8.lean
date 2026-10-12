/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 65.5.8: for properties `P` and `Q` satisfying the standing
base-change stability and fppf-locality conditions from Definition 65.5.1,
`P ≤ Q` induces the same implication for representable transformations of
presheaves over any scheme `S`. -/
@[stacks 02YO] #check
  (AlgebraicGeometry.Scheme.representableMorphismProperty_mono :
    ∀ {S : Scheme.{u}} {P Q : MorphismProperty Scheme.{u}},
      [P.IsStableUnderBaseChange] →
      [P.IsLocalAtTarget Scheme.fppfPrecoverage] →
      [Q.IsStableUnderBaseChange] →
      [Q.IsLocalAtTarget Scheme.fppfPrecoverage] →
      P ≤ Q →
      AlgebraicGeometry.Scheme.representableMorphismProperty S P ≤
        AlgebraicGeometry.Scheme.representableMorphismProperty S Q)
