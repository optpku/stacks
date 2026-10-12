/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (square : CommSq g' f' f g)
variable (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

/- 59.91.5.2 -/
@[stacks 0A2A] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq f g f' g' square E :
    (Derived.inverseImage g).obj ((Derived.directImage f).obj E) ⟶
      (Derived.directImage f').obj ((Derived.inverseImage g').obj E))
