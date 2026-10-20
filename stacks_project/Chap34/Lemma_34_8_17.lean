/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Big
import StacksCheckRecall

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 34.8.17: big ph morphisms of topoi compose along composition of morphisms over `S`. -/
@[stacks 0DBS] #check
  (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi_comp f.left g.left :
    MorphismOfTopoiIn.comp
      (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi g.left)
      (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi f.left) =
      AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi (f.left ≫ g.left))

end AlgebraicGeometry
