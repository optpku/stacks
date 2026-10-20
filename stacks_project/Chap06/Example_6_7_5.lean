/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafOfFunctions
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- The canonical presheaf `TopCat.presheafToTypes` has exactly the source sections and restriction
maps, as witnessed by `TopCat.presheafToTypes_obj` and `TopCat.presheafToTypes_map`. The theorem
`TopCat.Presheaf.toTypes_isSheaf` supplies the stated unique-gluing property, and
`TopCat.sheafToTypes` packages the same data as a sheaf. Recalling these owners avoids a parallel
project-local construction while exposing each source clause to downstream users.
-/

/- Example 6.7.5: for a family of sets `A : X → Type v` on a topological space `X`, the
presheaf `U ↦ ∀ x : U, A x.1` with restriction by precomposition along inclusions of opens is the
canonical presheaf `TopCat.presheafToTypes`. -/
@[stacks 006X "dependent-function presheaf associated to a family of sets"]
recall TopCat.presheafToTypes

/- The same presheaf satisfies the sheaf condition. In mathlib this is the canonical theorem
`TopCat.Presheaf.toTypes_isSheaf`. -/
@[stacks 006X "dependent functions satisfy the sheaf gluing condition"]
recall TopCat.Presheaf.toTypes_isSheaf

/- Companion recall: packaging the same presheaf together with its sheaf proof gives the mathlib
sheaf `TopCat.sheafToTypes`. -/
@[stacks 006X "packaged sheaf of dependent functions"]
recall TopCat.sheafToTypes

/- Companion recall: the value of the underlying presheaf on an open `U` is the product of the
fibers over points of `U`, formalized as dependent functions on `U`. -/
@[stacks 006X "sections over an open are products of the pointwise fibers"]
recall TopCat.presheafToTypes_obj

/- Companion recall: the restriction maps are given by restricting a dependent function along the
inclusion of opens. -/
@[stacks 006X "restriction maps restrict dependent functions along open inclusions"]
recall TopCat.presheafToTypes_map
