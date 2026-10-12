/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
variable (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X)

/- Lemma 83.3.5: in the situation of Lemma 83.3.3 there is an isomorphism of sheaves
(P.baseChange hφ f).quotientSheaf ≅ pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ)
identifying U'/R' with X' ×_X U/R. For the construction of quotient sheaves, see
Groupoids in Spaces, Section 78.19. -/
@[stacks 0DTF] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafBaseChangeIso P hφ f :
    (P.baseChange hφ f).quotientSheaf ≅
      pullback (AlgebraicGeometry.AlgebraicSpace.toSheaf.map f.left)
        (P.quotientSheafFactor hφ))
