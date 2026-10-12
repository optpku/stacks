/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.RingTheory.KrullDimension.Etale
public import ReasLib.Topology.KrullDimension.Local

/-!
# Local Krull dimensions under étale morphisms

This file records invariance results for local topological Krull dimensions and
Krull dimensions of stalk rings under étale morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom.EtaleAt

/-- An étale morphism at a point preserves the Krull dimension of the local ring at that
point and its image. -/
theorem ringKrullDim_stalk_eq {U V : Scheme.{u}} (f : U ⟶ V) (u : U)
    (h_etale : f.EtaleAt u) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (V.presheaf.stalk (f u)) := sorry

end Scheme.Hom.EtaleAt

namespace Etale

/-- An étale morphism preserves the Krull dimension of the local ring at every source point
and its image. -/
@[stacks 04N8]
theorem ringKrullDim_stalk_eq {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (V.presheaf.stalk (f u)) := sorry

/-- An étale morphism preserves the local topological Krull dimension at every source
point and its image. -/
@[stacks 04N4]
theorem topologicalKrullDimAt_eq {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    topologicalKrullDimAt u = topologicalKrullDimAt (f u) := sorry

end Etale

end AlgebraicGeometry
