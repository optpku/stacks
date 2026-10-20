/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.Topology.Sheaf.CompactOpen.Intersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open TopCat.Sheaf.CompactOpen.Intersection

universe u

variable (X : Scheme.{u}) [QuasiSeparatedSpace X]
variable (E : Set X) (S : Set (CompactOpens X))
variable (h : IsCompactOpenDirectedIntersection E S)
variable (F : (X : TopCat).Sheaf (Type u))

/- 40.15.0.1: if `X` is a quasi-separated scheme, `S` is a nonempty
downward-directed family of quasi-compact opens with intersection `E`, and `F` is a sheaf of
sets on `X`, then the canonical map `colimit (diagram S F) ⟶ target E F` is an isomorphism.
Here `IsCompactOpenDirectedIntersection E S` records nonemptiness, the intersection equation,
and the common-refinement condition. -/
@[stacks 0APH] #check
  (TopCat.Sheaf.CompactOpen.Intersection.comparison_isIso h F :
    IsIso (TopCat.Sheaf.CompactOpen.Intersection.comparison h F))
