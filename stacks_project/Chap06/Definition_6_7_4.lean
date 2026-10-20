/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Types.Constant
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

namespace TopCat

variable (X : TopCat.{u}) (A : Type u) (U V : Opens X) (hUV : U ≤ V)

/- The canonical owner is `CategoryTheory.constantSheaf`, while
`TopCat.Sheaf.Constant.toDiscrete` identifies it with the source's concrete model by
continuous, equivalently locally constant, maps into the discrete space on `A`. -/

/- Definition 6.7.4 (1): the constant sheaf with value `A` is the canonical sheafification of the
constant presheaf. -/
@[stacks 006W "canonical constant sheaf with value A"]
#check (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A

/- Definition 6.7.4 (2): the canonical constant sheaf is isomorphic to the source-facing
sheaf of continuous, equivalently locally constant, maps into the discrete space on `A`. -/
@[stacks 006W "constant sheaf identified with locally constant functions"]
#check TopCat.Sheaf.Constant.toDiscrete_isIso X A

/- Definition 6.7.4 (3): the source-facing model assigns to an open `U ⊆ X` the continuous
maps from `U` to the discrete space on `A`. -/
@[stacks 006W "sections as maps to the discrete space on A"]
#check (TopCat.presheafToTop_obj X (TopCat.discrete.obj A) (op U))

/- Definition 6.7.4 (4): maps to the discrete space on `A` are precisely locally constant
maps. -/
@[stacks 006W "continuous maps to discrete A are locally constant"]
#check (IsLocallyConstant.iff_continuous :
  ∀ f : U → TopCat.discrete.obj A, IsLocallyConstant f ↔ Continuous f)

/- Definition 6.7.4 (5): restriction along an inclusion of opens is precomposition with the
inclusion map. -/
@[stacks 006W "restriction maps are restrictions of functions"]
#check TopCat.Presheaf.Constant.discreteContinuous_restrict_apply (A := A) hUV

end TopCat
