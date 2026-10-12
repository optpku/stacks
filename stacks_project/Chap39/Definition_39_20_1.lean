/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 39.20.1: for a pre-relation on `U` over `S`, the quotient sheaf `U/R`
is obtained by sheafifying its quotient presheaf; in the standard topology this uses
`τ.overTopology S`. -/
@[stacks 02VG] #check
  (@AlgebraicGeometry.Scheme.PreRelation.quotientSheaf :
    ∀ {S : Scheme.{u}} {U : Over S} (J : GrothendieckTopology (Over S)),
      Scheme.PreRelation U → Sheaf J (Type (u + 1)))

/- The underlying presheaf of the quotient sheaf is the sheafification of the
universe-raised quotient presheaf. -/
#check
  (@AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_val :
    ∀ {S : Scheme.{u}} {U : Over S} (J : GrothendieckTopology (Over S))
      (P : Scheme.PreRelation U),
      (P.quotientSheaf J).obj =
        sheafify J (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}))

section

variable {S : Scheme.{u}} (τ : StandardTopology)
variable (G : Grp (Over S)) (U : AlgebraicGeometry.GroupScheme.Action G)

/- For an action of `G/S` on `U`, the notation `U/G` refers to the quotient sheaf of
the associated action groupoid pre-relation. -/
#check
  (((AlgebraicGeometry.GroupoidScheme.ofAction G U).toPreRelation).quotientSheaf
    (τ.overTopology S) : Sheaf (τ.overTopology S) (Type (u + 1)))

end
