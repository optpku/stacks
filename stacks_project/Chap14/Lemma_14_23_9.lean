/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateAcyclic
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Comparison
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Lemma 14.23.9

@stack 019C

The quasi-isomorphism and degenerate-complex acyclicity statements are consequences of the
reusable normalized-plus-degenerate decomposition. The acyclic cokernel is retained as a
supporting consequence.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped DoldKan

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (V : SimplicialObject A)

/- Lemma 14.23.9 (1): the source-signed normalized-Moore inclusion is a quasi-isomorphism. -/
@[stacks 019C "Lemma 14.23.9 (1)"]
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.quasiIso V :
  QuasiIso (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.app V))

@[stacks 019C "source-signed normalized inclusion acyclic cokernel"]
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.cokernel.acyclic V)

/- Lemma 14.23.9 (2): the source degenerate summand is acyclic. -/
@[stacks 019C "Lemma 14.23.9 (2)"]
#check (degenerateComplex.acyclic V : D[V].Acyclic)

/- The d₀/Q∞ formulations remain convention-specific companions. -/
#check (AlgebraicTopology.DoldKan.QInfty.acyclic V :
  (AlgebraicTopology.DoldKan.QInfty.image V).Acyclic)

/- The acyclic summand is canonically represented by the `QInfty` image; this check keeps the
source bridge independent of the degreewise implementation. -/
#check (AlgebraicTopology.DoldKan.QInfty.image V)
variable (n : ℕ)
#check (AlgebraicTopology.DoldKan.QInfty.evalImageIso V n)
#check (AlgebraicTopology.DoldKan.QInfty.degreeSubobject V n)
#check (AlgebraicTopology.DoldKan.QInfty.degreeIso V n)
#check (AlgebraicTopology.DoldKan.QInfty.degreeProjection V n)
#check (AlgebraicTopology.DoldKan.QInfty.degreeSubobject_eq V n)

#check (degenerateComplex.contraction V)
#check (degenerateComplex.contractible V)
#check (AlgebraicTopology.DoldKan.QInfty.contraction V)
#check (AlgebraicTopology.DoldKan.QInfty.contractible V)
#check (degenerateComplex.contractible V).acyclic
#check Homotopy.equivZero (degenerateComplex.contraction V)
#check (_root_.AlgebraicTopology.normalizedMooreComplex.inclusion.cokernel.acyclic V)

end AlgebraicTopology.DoldKan
