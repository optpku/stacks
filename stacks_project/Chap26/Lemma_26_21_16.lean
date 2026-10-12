/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.AffineOpen
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [S.IsSeparated]
variable (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)

/- Lemma 26.21.16: a scheme separated over a separated target is separated. -/
@[stacks 01KW] #check Hom.source_isSeparated f

/- Consequently intersections of affine opens are affine. -/
@[stacks 01KW] #check f.isAffineOpen_inf hU hV

/- The intersection maps as a closed subscheme of the product. -/
@[stacks 01KW] #check f.interToProduct_isClosedImmersion U V

/- Explicit-witness bridges remain available when separatedness is not an ambient instance. -/
#check IsAffineOpen.inf_of_isSeparated
#check Opens.isClosedImmersion_interToProduct_of_isSeparated

end AlgebraicGeometry.Scheme
