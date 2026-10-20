/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
import StacksCheckRecall

/-!
@stack 07KA

# Source-facing recall for Example 14.26.3

The reusable `Homotopy.ofEq` construction transports mathlib's canonical constant homotopy along
an equality of simplicial morphisms.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y} (hfg : f = g)

/- Example 14.26.3: equal morphisms are joined by the transported constant simplicial
homotopy. -/
@[stacks 07KA]
#check (Homotopy.ofEq hfg : Homotopy f g)

#check (fun {n : ℕ} (i : Fin (n + 1)) ↦ Homotopy.ofEq.h hfg i)
#check (Homotopic.of_eq hfg : Homotopic f g)

end CategoryTheory.SimplicialObject
