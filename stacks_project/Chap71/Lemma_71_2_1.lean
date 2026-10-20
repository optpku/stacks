module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints

/-!
# Lemma 71.2.1

Weak association of a point of an algebraic space to a quasi-coherent module is
independent of the étale scheme chart and equivalent to weak association of the
maximal ideal of the étale local ring to the module stalk. On a locally
Noetherian algebraic space the associated-point variants are equivalent as well.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.2.1: weak association on some or every étale scheme chart is equivalent
to weak association of the maximal ideal at the geometric étale stalk. -/
@[stacks 0CTW] #check (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_etaleChart_tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X),
    List.TFAE [existsEtaleWeakAss F x, forallEtaleWeakAss F x, etaleStalkWeakAss F x])

/- Lemma 71.2.1: on a locally Noetherian algebraic space, the three weak-association
conditions are also equivalent to the three association conditions. -/
@[stacks 0CTW] #check (AlgebraicGeometry.AlgebraicSpace.Modules.associatedPoints_etaleChart_tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X),
    List.TFAE [existsEtaleWeakAss F x, forallEtaleWeakAss F x, etaleStalkWeakAss F x,
      existsEtaleAss F x, forallEtaleAss F x, etaleStalkAss F x])
