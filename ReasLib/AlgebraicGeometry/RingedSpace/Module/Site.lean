/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Abelian.Over
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice-site conditions for modules on ringed spaces

The topology of a ringed space canonically supplies the one-level and iterated slice-site
instances used by local properties of module sheaves.  This leaf exposes the topology owners
without introducing ring-sheaf-dependent wrapper classes.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}}

/-- The inverse-image functor on opens attached to a morphism of ringed spaces is continuous for
the canonical Grothendieck topologies. This bridge keeps typeclass search from having to unfold the
bundled ringed-space morphism. -/
instance opensMap_isContinuous (f : X ⟶ Y) :
    (Opens.map f.hom.base).IsContinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
  instIsContinuousOpensCarrierMapGrothendieckTopology f.hom.base

/-- The inverse-image functor on opens is final. Naming this canonical instance avoids repeatedly
reconstructing its right-adjoint presentation when module-sheaf pullback APIs require finality. -/
@[stacks 03DF "inverse image on opens is final"]
instance opensMap_final (f : X ⟶ Y) :
  (Opens.map f.hom.base).Final :=
  final_of_representablyFlat (Opens.map f.hom.base)

end AlgebraicGeometry.RingedSpace.Hom

