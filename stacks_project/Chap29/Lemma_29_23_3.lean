/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 29.23.3 (1): a composition of open morphisms is open. -/
@[stacks 02V2] #check
  (CategoryTheory.MorphismProperty.comp_mem
      (AlgebraicGeometry.topologically (@IsOpenMap)) f g :
    IsOpenMap f.base → IsOpenMap g.base → IsOpenMap (f ≫ g).base)

/- Lemma 29.23.3 (2): a composition of universally open morphisms is universally open. -/
@[stacks 02V2] #check
  (CategoryTheory.MorphismProperty.comp_mem (@AlgebraicGeometry.UniversallyOpen) f g :
    UniversallyOpen f → UniversallyOpen g → UniversallyOpen (f ≫ g))

end AlgebraicGeometry
