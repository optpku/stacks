/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.UniversallyClosed

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.30.3: Let `S` be a scheme and let `p : X ⟶ S` be presented as the relative
projective spectrum of a quasi-coherent graded algebra. If its base-to-degree-zero algebra maps
are integral and the graded algebra is finite type over degree zero, then `p` is universally
closed. -/
@[stacks 07ZZ] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.IntegralDegreeZeroAlgebra.universallyClosed :
    ∀ {S X : Scheme.{u}} {p : X ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p},
      P.IntegralDegreeZeroAlgebra →
        P.FiniteTypeAsDegreeZeroAlgebra →
          UniversallyClosed p)
