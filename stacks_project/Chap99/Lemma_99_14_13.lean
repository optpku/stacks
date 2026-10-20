module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Polarized.OpennessOfVersality

/-!
# Lemma 99.14.13

The stack in groupoids Polarized satisfies openness of versality over `specZ`.
After the base change of Remark 99.14.5, the same axiom holds over any
Noetherian base scheme `S`.
-/

@[expose] public section

universe u

/- Lemma 99.14.13: the stack of polarized proper schemes satisfies openness
of versality over `Spec ℤ`. -/
@[stacks 0D4V] #check
  (AlgebraicGeometry.Polarized.instOpennessOfVersality.{u} :
    AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
      AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ.{u})

/- After base change, openness of versality holds over every Noetherian
base scheme. -/
#check
  (AlgebraicGeometry.Polarized.instOpennessOfVersality_over :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S],
      AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
        (AlgebraicGeometry.Polarized.toGroupoidsOver S))
